//! Buffers for single-buffer and vectored I/O which tracking initializedness and how much has been
//! filled. Container types pointing to possibly-uninitialized memory such as
//! `Vec<MaybeUninit<u8>>`, `IoBox<Uninitialized>`, or `Box<[MaybeUninit<u8>]> can be transformed
//! into their initialized variants via the [`Initialize`] trait, within requiring unsafe code.
//!
//! This is an implementation of an API similar to what has been proposed in [this
//! RFC](https://github.com/sfackler/rfcs/blob/read-buf/text/0000-read-buf.md).

use core::mem::MaybeUninit;

use crate::{Initialize, InitializeIndirect, InitializeExt};

pub trait Source {
    fn fill<T: InitializeIndirect>(&mut self, buf: BufferRef<T>);
}
pub trait FallibleSource {
    type Error;

    fn try_fill<T: InitializeIndirect>(&mut self, buf: BufferRef<T>) -> Result<(), Self::Error>;
}

pub trait FullSource {}
pub unsafe trait TrustedFullSource {}

// TODO: Asynchronous sources. These would only function as convenience wrappers, but might be
// useful when async fn in traits.

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Fill {
    byte: u8,
}

impl Fill {
    #[inline]
    pub const fn from_byte(byte: u8) -> Self {
        Self { byte }
    }
    #[inline]
    pub const fn byte(self) -> u8 {
        self.byte
    }
}

impl Source for Fill {
    fn fill<T: InitializeIndirect>(&mut self, mut buf: BufferRef<T>) {
        buf.unfilled_part_mut().init_by_filling(self.byte());

        // SAFETY: The only safety invariant, that all previously-uninitialized bytes must be
        // initialized, is upheld since we have filled them.
        unsafe { buf.advance_to_end(); }
    }
}
impl FallibleSource for Fill {
    type Error = core::convert::Infallible;

    fn try_fill<T: InitializeIndirect>(&mut self, buf: BufferRef<T>) -> Result<(), Self::Error> {
        Ok(self.fill(buf))
    }
}
impl FullSource for Fill {}
unsafe impl TrustedFullSource for Fill {}

#[cfg(feature = "nightly")]
pub struct FillConst<const BYTE: u8>;

#[cfg(feature = "nightly")]
impl<const BYTE: u8> Source for FillConst<BYTE> {
    fn fill<T: InitializeIndirect>(&mut self, buf: BufferRef<T>) {
        Fill::from_byte(BYTE).fill(buf)
    }
}
#[cfg(feature = "nightly")]
impl<const BYTE: u8> FallibleSource for FillConst<BYTE> {
    type Error = core::convert::Infallible;

    fn try_fill<T: InitializeIndirect>(&mut self, buf: BufferRef<T>) -> Result<(), Self::Error> {
        Fill::from_byte(BYTE).try_fill(buf)
    }
}
#[cfg(feature = "nightly")]
impl<const BYTE: u8> FullSource for FillConst<BYTE> {}

#[derive(Debug)]
pub struct Limit<S> {
    inner: S,
    limit: usize,
}
impl<S> Source for Limit<S>
where
    S: Source,
{
    fn fill<T: InitializeIndirect>(&mut self, mut buf: BufferRef<T>) {
        let uninit_part_mut = buf.uninit_part_mut();
        let len = core::cmp::min(uninit_part_mut.len(), self.limit);
        let mut smaller_buffer = Buffer::new(&mut uninit_part_mut[..len]);
        let smaller_buffer = smaller_buffer.by_ref();

        self.inner.fill(smaller_buffer)
    }
}

#[cfg(feature = "std")]
pub struct Io<S> {
    inner: S,
}

#[cfg(feature = "std")]
impl<S> Source for Io<S>
where
    S: std::io::Read,
{
    fn fill<T: InitializeIndirect>(&mut self, buf: BufferRef<T>) {
        match self.try_fill(buf) {
            Ok(()) => (),
            Err(_) => return,
        }
    }
}
#[cfg(feature = "std")]
impl<S> FallibleSource for Io<S>
where
    S: std::io::Read,
{
    type Error = std::io::Error;

    fn try_fill<T: InitializeIndirect>(&mut self, mut buf: BufferRef<T>) -> Result<(), Self::Error> {
        // TODO: Compatibility with the ongoing RFC, https://github.com/rust-lang/rfcs/pull/2930.
        // We don't want to zero the buffer even if it's already initialized!
        let initialized = buf.uninit_part_mut().init_by_filling(0);

        match self.inner.read(initialized) {
            Ok(count) => {
                assert!(count <= buf.bytes_to_fill());
                Ok(unsafe { buf.advance(count) })
            }
            Err(error) => Err(error),
        }
    }
}

pub struct Sources<I> {
    inner: I,
}

impl<I> Source for Sources<I>
where
    I: Iterator,
    I::Item: Source,
{
    fn fill<T: InitializeIndirect>(&mut self, mut buf: BufferRef<T>) {
        while let Some(mut source) = self.inner.next() {
            source.fill(buf.by_ref());
        }
    }
}
impl<I> FallibleSource for Sources<I>
where
    I: Iterator,
    I::Item: FallibleSource,
{
    type Error = <<I as Iterator>::Item as FallibleSource>::Error;

    fn try_fill<T: InitializeIndirect>(&mut self, mut buf: BufferRef<T>) -> Result<(), Self::Error> {
        while let Some(mut source) = self.inner.next() {
            source.try_fill(buf.by_ref())?;
        }

        Ok(())
    }
}

pub struct Buffers<T> {
    inner: T,
    // TODO: Use a trait to omit this field when the type already is initialized.
    // NOTE: We use this counter __only internally__. Namely, in order to avoid unnecessary bounds
    // checking when indexing buffers, this must not be changed to any arbitrary value.
    // TODO: Use some integer generic type (or perhaps simply a platform-specific type alias), to
    // reduce the memory footprint when IOV_MAX happens to be less than 65536. Or at least just
    // 32-bit.
    bytes_filled_for_vector: usize,
    // TODO: Use specialization to omit this field when there is only one buffer..
    vectors_filled: usize,
}
/// A buffer tracking a container type that dereferences into a slice of possibly-uninitialized
/// bytes, and how many bytes have been initialized and filled, respectively. The inner data can
/// always be moved out as uninitialized, but when the buffer _has_ been fully initialized, the
/// buffer can be turned into the initialized equivalent.
pub struct Buffer<T> {
    // The inner data, which must implement `Initialize` to do anything useful with. The inner data
    // points to a slice of possibly uninitialized bytes, and must always return the same slice in
    // the trait.
    inner: T,
    bytes_initialized: usize,
    bytes_filled: usize,
}

/// A reference to a [`Buffer`].
pub struct BufferRef<'buffer, T> {
    // NOTE: The reference here is private, and never accessed using the API, _since we don't want
    // an API user to be able to replace a `&mut Buffer` with a completely different one_.
    inner: &'buffer mut Buffer<T>,
}

impl<T> Buffer<T> {
    /// Create a new buffer, defaulting to not being initialized, nor filled. Prefer [`new_init`]
    /// if the buffer is already initialized.
    #[inline]
    pub const fn new(inner: T) -> Self {
        Self {
            inner,
            bytes_filled: 0,
            bytes_initialized: 0,
        }
    }
    /// Move out the inner buffer, together with the initializedness cursor, as well as the
    /// filledness cursor.
    #[inline]
    pub fn into_raw_parts(self) -> (T, usize, usize) {
        let Self { inner, bytes_initialized, bytes_filled } = self;

        (inner, bytes_initialized, bytes_filled)
    }
    /// Move out the inner buffer, being uninitialized or initialized based on whatever it was when
    /// this buffer was constructed.
    ///
    /// Use [`try_into_init`] if the buffer is initialized.
    #[inline]
    pub fn into_inner(self) -> T {
        self.inner
    }

    /// Get the number of bytes that are currently filled, within the buffer. Note that this is
    /// different from the number of initialized bytes; use [`bytes_initialized`] for that.
    #[inline]
    pub fn bytes_filled(&self) -> usize {
        self.bytes_filled
    }
    #[inline]
    pub fn bytes_initialized(&self) -> usize {
        self.bytes_initialized
    }

    #[inline]
    pub fn by_ref<'buffer>(&'buffer mut self) -> BufferRef<'buffer, T> {
        BufferRef { inner: self }
    }
}

impl<T> Buffer<T>
where
    T: Initialize,
{
    fn debug_assert_valid_len(&self) {
        debug_assert!(self.bytes_filled() <= self.capacity());
        debug_assert!(self.bytes_initialized() <= self.capacity());
        debug_assert!(self.bytes_filled() <= self.bytes_initialized());
    }

    /// Retrieve a slice of a possibly uninitialized bytes, over the entire buffer.
    #[inline]
    pub fn all_uninit(&self) -> &[MaybeUninit<u8>] {
        self.inner.as_maybe_uninit_slice()
    }
    /// Retrieve a mutable slice of a possibly uninitialized bytes, over the entire buffer.
    ///
    /// # Safety
    ///
    /// This is unsafe, because the caller must not de-initialize the slice as the API also
    /// promises the initialized region to always actually be initialized.
    #[inline]
    pub unsafe fn all_uninit_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.by_ref().all_uninit_mut()
    }
    /// Get the total size of the buffer that is being initialized.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.all_uninit().len()
    }
    /// Get the number of bytes that may be filled before the buffer is full.
    #[inline]
    pub fn bytes_to_fill(&self) -> usize {
        debug_assert!(self.capacity() >= self.bytes_filled);
        self.capacity().wrapping_sub(self.bytes_filled)
    }
    /// Get the number of bytes that must be filled before the buffer gets fully initialized, and
    /// can be turned into an initialized type (e.g. `Box<[u8]>`).
    #[inline]
    pub fn bytes_to_init(&self) -> usize {
        debug_assert!(self.capacity() >= self.bytes_initialized);
        self.capacity().wrapping_sub(self.bytes_initialized)
    }
    #[inline]
    pub fn is_completely_filled(&self) -> bool {
        self.bytes_filled() == self.capacity()
    }
    #[inline]
    pub fn is_partially_filled(&self) -> bool {
        self.bytes_filled() > 0
    }
    #[inline]
    pub fn is_completely_initialized(&self) -> bool {
        self.bytes_initialized() == self.capacity()
    }
    #[inline]
    pub fn is_partially_initialized(&self) -> bool {
        self.bytes_initialized() > 0
    }
    #[inline]
    pub fn uninit_part(&self) -> &[MaybeUninit<u8>] {
        let all = self.all_uninit();

        // Validate that bytes_filled is valid, when _debug assertions_ are enabled.
        self.debug_assert_valid_len();

        // NOTE: We use unsafe to eliminate unnecessary bounds checking. This may be negligible for
        // many scenarios, but we want to keep this interface zero-cost.
        unsafe {
            // SAFETY: We uphold the safety invariants:
            //
            // 1) the pointer belongs to the same allocated object, since we are simply taking a
            //    subslice of an existing slice;
            // 2) the offset multiplied by the item size cannot overflow an isize. This is
            //    impossible, since the size of u8 is 1, and thus the only requirement is for
            //    bytes_filled not to overflow an isize, which it cannot do;
            // 3) the resulting pointer cannot overflow the pointer size. This is also impossible,
            //    since for `all` to be a valid slice, it must not wrap around in address space,
            //    between its start and end range.
            let ptr = all.as_ptr().add(self.bytes_initialized);
            let len = all.len().wrapping_sub(self.bytes_initialized);

            // SAFETY: This is safe, because:
            //
            // 1) the data is valid for the entire memory range, since we are taking a subset of an
            //    already well-defined slice. Everything is therefore contained within a single
            //    allocation object, and the pointer is already non-null, since the pointer
            //    addition must not overflow;
            // 2) while no byte whatsoever in [bytes_filled, len) is guaranteed to be initialized,
            //    MaybeUninit is special and is always considered initialized (even though the
            //    value it wraps has no such guarantee);
            // 3) the value is not mutated for the lifetime of the slice, since the slice is owned
            //    by this struct, and there cannot exist a mutable borrow within this borrow for
            //    the anonymous lifetime `'_`;
            // 4) the number of bytes filled is not larger than isize::MAX. This is checked every
            //    time bytes_filled changes.
            core::slice::from_raw_parts(ptr, len)
        }
    }
    #[inline]
    pub fn init_part(&self) -> &[u8] {
        // Validate that bytes_filled is valid, when _debug assertions_ are enabled.
        self.debug_assert_valid_len();

        // NOTE: Use of unsafe is only to eliminate bounds checks and maintain zero-cost.
        unsafe {
            let ptr = self.all_uninit().as_ptr();
            let len = self.bytes_initialized;

            // SAFETY: This is safe, due to the same invariants as with `uninit_part`, except for
            // the initialization invariant. We uphold this, by guaranteeing that the entire slice
            // we construct, is initialized, since this is a contract merely from using this
            // wrapper. We also uphold the validity variant, which is somewhat different in this
            // case, since we know that bytes_filled must be smaller than or equal to the size of
            // the slice.
            core::slice::from_raw_parts(ptr as *const u8, len)
        }
    }

    // NOTE: We extract pointers to avoid multiple mutable aliases when invoking
    // core::slice::from_raw_parts_mut.
    #[inline]
    pub fn uninit_part_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        let (orig_ptr, orig_len) = unsafe {
            let orig = self.all_uninit_mut();
            (orig.as_mut_ptr(), orig.len())
        };
        unsafe {
            // Validate that bytes_filled is correct when debug assertions are enabled.
            self.debug_assert_valid_len();

            // SAFETY: This pointer arithmetic operation, is safe for the same reasons as with
            // `uninit_part`.
            let ptr = orig_ptr.add(self.bytes_initialized);
            let len = orig_len.wrapping_sub(self.bytes_initialized);

            // SAFETY: This is safe for the exact same reasons as with `uninit_part`, but that
            // there must not be any reference _at all_ to the inner slice. This is upheld by
            // knowing that we have already borrowed the owner of the slice mutably.
            core::slice::from_raw_parts_mut(ptr, len)
        }
    }

    #[inline]
    pub fn init_part_mut(&mut self) -> &mut [u8] {
        let orig_ptr = unsafe {
            self.all_uninit_mut().as_mut_ptr()
        };

        unsafe {
            let ptr = orig_ptr;
            let len = self.bytes_initialized;

            // SAFETY: This is safe for the exact same reasons as with `init_part`, except that we
            // also ensure that there is no access whatsoever to the inner data, since we are
            // borrowing `self` mutably.
            core::slice::from_raw_parts_mut(ptr as *mut u8, len)
        }
    }
    #[inline]
    pub fn filled_part(&self) -> &[u8] {
        unsafe {
            self.debug_assert_valid_len();

            let ptr = self.all_uninit().as_ptr();
            let len = self.bytes_filled;

            core::slice::from_raw_parts(ptr as *const u8, len)
        }
    }
    #[inline]
    pub fn filled_part_mut(&self) -> &mut [u8] {
        let orig_ptr = unsafe {
            self.all_uninit_mut().as_mut_ptr()
        };

        unsafe {
            self.debug_assert_valid_len();

            let ptr = orig_ptr;
            let len = self.bytes_filled;

            core::slice::from_raw_parts_mut(ptr as *mut u8, len)
        }
    }
    #[inline]
    pub fn unfilled_part(&self) -> &[MaybeUninit<u8>] {
        let (orig_ptr, orig_len) = {
            let orig = self.all_uninit();

            (orig.as_ptr(), orig.len())
        };

        unsafe {
            self.debug_assert_valid_len();

            let ptr = orig_ptr.add(self.bytes_filled);
            let len = orig_len.wrapping_sub(self.bytes_filled);

            core::slice::from_raw_parts(ptr, len)
        }
    }
    #[inline]
    pub fn unfilled_part_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        let (orig_ptr, orig_len) = unsafe {
            let orig = self.all_uninit_mut();
            (orig.as_mut_ptr(), orig.len())
        };

        unsafe {
            self.debug_assert_valid_len();

            let ptr = orig_ptr.add(self.bytes_filled);
            let len = orig_len.wrapping_sub(self.bytes_filled);

            core::slice::from_raw_parts_mut(ptr, len)
        }
    }
    #[inline]
    pub fn filled_unfilled_parts(&self) -> (&[u8], &[MaybeUninit<u8>]) {
        (self.filled_part(), self.unfilled_part())
    }
    #[inline]
    pub fn init_uninit_parts(&self) -> (&[u8], &[MaybeUninit<u8>]) {
        (self.init_part(), self.uninit_part())
    }

    #[inline]
    pub fn filled_unfilled_parts_mut(&mut self) -> (&mut [u8], &mut [MaybeUninit<u8>]) {
        let (all_ptr, all_len) = unsafe {
            let all = self.all_uninit_mut();

            (all.as_mut_ptr(), all.len())
        };

        unsafe {
            self.debug_assert_valid_len();

            let filled_base_ptr = all_ptr as *mut u8;
            let filled_len = self.bytes_filled;

            let unfilled_base_ptr = all_ptr.add(self.bytes_filled);
            let unfilled_len = all_len.wrapping_sub(self.bytes_filled);

            let filled = core::slice::from_raw_parts_mut(filled_base_ptr, filled_len);
            let unfilled = core::slice::from_raw_parts_mut(unfilled_base_ptr, unfilled_len);

            (filled, unfilled)
        }
    }
    #[inline]
    pub fn init_uninit_parts_mut(&mut self) -> (&mut [u8], &mut [MaybeUninit<u8>]) {
        let (all_ptr, all_len) = unsafe {
            let all = self.all_uninit_mut();

            (all.as_mut_ptr(), all.len())
        };

        unsafe {
            self.debug_assert_valid_len();

            let init_base_ptr = all_ptr as *mut u8;
            let init_len = self.bytes_initialized;

            let uninit_base_ptr = all_ptr.add(self.bytes_initialized);
            let uninit_len = all_len.wrapping_sub(self.bytes_initialized);

            let init = core::slice::from_raw_parts_mut(init_base_ptr, init_len);
            let uninit = core::slice::from_raw_parts_mut(uninit_base_ptr, uninit_len);
            
            (init, uninit)
        }
    }
    /// Advance the internal cursor, that divides the initialized and uninitialized parts.
    ///
    /// # Safety
    ///
    /// For this to be safe, the following safety invariants must be upheld:
    ///
    /// * `count`, when added to the current value of `bytes_filled` must not overflow the size of
    ///   the full slice (which in turn must not overflow the size of `isize::MAX`);
    /// * at least `count` consecutive bytes of the uninitialized part, must have been written to.
    ///
    /// # Panics
    ///
    /// This will panic rather than causing UB, when _debug assertions_ are enabled. That is, it
    /// will panic if the count, when added with the current number of bytes filled, neither
    /// overflows `isize::MAX`, nor the total size of the slice.
    #[inline]
    pub unsafe fn assume_init_by(&mut self, count: usize) {
        self.bytes_initialized = self.bytes_initialized.wrapping_add(count);
    }

    /// Advance the internal cursor to the end, marking the entire buffer as initialized.
    ///
    /// This method is recommended over calling [`advance`] directly, when all bytes have been
    /// written to, since no arithmetic invariants need to be upheld.
    ///
    /// # Safety
    ///
    /// This is unsafe for the sole reason that every byte must have been written to for this to be
    /// safe.
    #[inline]
    pub unsafe fn assume_init_all(&mut self) {
        self.bytes_initialized = self.capacity();
    }

    /// Assume that the entire buffer has been initialized, returning the inner initialized type.
    ///
    /// # Safety
    ///
    /// This is unsafe since it must uphold the initialization invariant; every byte of the
    /// uninitialized part must have been written to.
    #[inline]
    pub unsafe fn assume_init(self) -> T::Initialized {
        self.inner.assume_init()
    }
    /// Revert the internal cursor to 0, forgetting about the initialized bytes.
    #[inline]
    pub fn revert_to_start(&mut self) {
        self.by_ref().revert_to_start()
    }
    /// Fill the buffer from a source, advancing until the buffer cannot be filled anymore.
    ///
    /// When the buffer is full, [`try_into_init`] shall succeed. It is however recommended to use
    /// [`init_from_source`] or [`try_init_from_source`] to do a full initialization in one step.
    pub fn fill_from_source(&mut self, mut source: impl Source) {
        source.fill(self.by_ref())
    }
    /// Fill the buffer from a fallible source, advancing until the source either is out of bytes,
    /// or if an error is encountered.
    pub fn fill_from_fallible_source<S>(&mut self, mut source: S) -> Result<(), S::Error>
    where
        S: FallibleSource,
    {
        source.try_fill(self.by_ref())
    }
    /// Attempt to unwrap the inner container storing the bytes, and transform it into its
    /// initialized counterpart, if and only if the buffer is fully initialized.
    #[inline]
    pub fn try_into_init(self) -> Result<T::Initialized, Self> {
        if self.is_completely_filled() {
            Ok(unsafe { self.assume_init() })
        } else {
            Err(self)
        }
    }
    pub fn try_init_from_source(mut self, source: impl Source) -> Result<T::Initialized, Self> {
        self.fill_from_source(source);
        self.try_into_init()
    }
    pub fn init_from_source(mut self, source: impl Source + FullSource) -> T::Initialized {
        self.fill_from_source(source);

        match self.try_into_init() {
            Ok(t) => t,
            Err(_) => unreachable!("trait contract broken: FullSource impl must guarantee that all buffers are fully initialized"),
        }
    }
    // TODO: try_init_from_fallible_source, etc.

    // TODO: Use specialization to merge init_from_source and init_from_trusted_source into a
    // single function.
    pub fn init_from_trusted_source(mut self, source: impl Source + TrustedFullSource) -> T::Initialized {
        self.fill_from_source(source);

        unsafe { self.assume_init() }
    }
    pub fn init_by_filling(self, byte: u8) -> T::Initialized {
        self.init_from_trusted_source(Fill::from_byte(byte))
    }
    pub fn init_by_zeroing(self) -> T::Initialized {
        self.init_by_filling(0_u8)
    }
}
impl<T> Buffers<T>
where
    T: InitializeIndirect,
{
    #[inline]
    fn all_vectors_uninit(&self) -> &[T::UninitItem] {
        self.inner.as_maybe_uninit_slices()
    }

    #[inline]
    fn all_vectors_uninit_mut(&mut self) -> &mut [T::UninitItem] {
        self.inner.as_maybe_uninit_slices_mut()
    }

    #[inline]
    pub fn current_buffer(&self) -> Option<&[MaybeUninit<u8>]> {
        Some(self.inner.as_maybe_uninit_slices().get(self.vectors_filled)?.as_maybe_uninit_slice())
    }
    fn debug_assert_valid_len(&self) {
        debug_assert!(self.current_buffer().map_or(true, |current_buffer| current_buffer.len() >= self.bytes_filled_for_vector));
        debug_assert!(self.bytes_filled_for_vector <= isize::MAX as usize);
        debug_assert!(self.inner.as_maybe_uninit_slices().len() >= self.vectors_filled);
    }

    #[inline]
    pub fn total_vector_count(&self) -> usize {
        self.inner.as_maybe_uninit_slices().len()
    }

    #[inline]
    pub fn vectors_filled(&self) -> usize {
        self.vectors_filled
    }

    #[inline]
    pub fn vectors_to_fill(&self) -> usize {
        self.total_vector_count().wrapping_sub(self.vectors_filled())
    }

    /// Counts the bytes that must be filled before the whole buffer is initialized.
    #[inline]
    pub fn count_bytes_to_fill(&self) -> usize {
        self.all_uninit_slices().iter().map(|buffer| buffer.as_maybe_uninit_slice().len()).sum()
    }

    #[inline]
    pub fn all_uninit_slices(&self) -> &[T::UninitItem] {
        self.inner.as_maybe_uninit_slices()
    }
    #[inline]
    pub fn all_uninit_slices_mut(&mut self) -> &mut [T::UninitItem] {
        self.inner.as_maybe_uninit_slices_mut()
    }

    #[inline]
    pub unsafe fn current_vector_all_mut(&mut self) -> Option<&mut [MaybeUninit<u8>]> {
        Some(self.inner.as_maybe_uninit_slices_mut().get(self.vectors_filled)?.as_maybe_uninit_slice_mut())
    }
    #[inline]
    pub unsafe fn advance(&mut self, mut count: usize) -> usize {
        let mut bytes_advanced = 0;

        loop {
            let current_uninit_part_len = match self.current_vector_uninit_part() {
                Some(slice) => slice.len(),
                None => break,
            };
            if count >= current_uninit_part_len {
                self.vectors_filled = self.vectors_filled
                    .checked_add(1)
                    .expect("reached usize::MAX when incrementing the buffer index");
                self.bytes_filled_for_vector = 0;

                count -= current_uninit_part_len;

                bytes_advanced -= current_uninit_part_len;
                continue;
            } else {
                self.bytes_filled_for_vector += current_uninit_part_len;
            }
        }

        bytes_advanced
    }
}

impl<'a> Buffer<&'a mut [u8]> {
    #[inline]
    pub fn from_slice_mut(slice: &'a mut [u8]) -> Self {
        unsafe { Self::new(slice).advance_init_to_end() }
    }
}
impl<'a> Buffer<&'a mut [MaybeUninit<u8>]> {
    #[inline]
    pub fn from_uninit_slice_mut(slice: &'a mut [MaybeUninit<u8>]) -> Self {
        Self::new(slice)
    }
}

impl<'buffer, T> BufferRef<'buffer, T> {
    #[inline]
    pub fn bytes_filled(&self) -> usize {
        self.inner.bytes_filled()
    }

    /// Reborrow the inner buffer, getting a buffer reference with a shorter lifetime.
    #[inline]
    pub fn by_ref<'shorter>(&'shorter mut self) -> BufferRef<'shorter, T> {
        BufferRef {
            inner: self.inner,
        }
    }
}

impl<'buffer, T> BufferRef<'buffer, T>
where
    T: Initialize,
{
    #[inline]
    pub fn all_uninit(&self) -> &[MaybeUninit<u8>] {
        self.inner.all_uninit()
    }
    #[inline]
    pub unsafe fn all_uninit_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.inner.all_uninit_mut()
    }
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }
    #[inline]
    pub fn bytes_to_fill(&self) -> usize {
        self.inner.bytes_to_fill()
    }
    #[inline]
    pub fn uninit_part(&self) -> &[MaybeUninit<u8>] {
        self.inner.uninit_part()
    }
    #[inline]
    pub fn init_part(&self) -> &[u8] {
        self.inner.init_part()
    }
    #[inline]
    pub fn uninit_part_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.inner.uninit_part_mut()
    }
    #[inline]
    pub fn init_part_mut(&mut self) -> &mut [u8] {
        self.inner.init_part_mut()
    }
    #[inline]
    pub unsafe fn advance_init(&mut self, count: usize) {
        self.inner.advance()
    }
    #[inline]
    pub unsafe fn advance_to_end(&mut self) {
        *self.bytes_filled = self.bytes_to_fill();
    }
    #[inline]
    pub fn revert_to_start(&mut self) {
        *self.bytes_filled = 0;
    }
    #[inline]
    pub fn init_by_filling(&mut self, byte: u8) {
        Fill::from_byte(byte).fill(self.by_ref())
    }
    #[inline]
    pub fn init_by_zeroing(&mut self) {
        self.init_by_filling(0_u8)
    }
}

enum Ref<'buffer, T> {
    Single(&'buffer mut Buffer<T>),
    Multiple(&'buffer mut Buffers<T>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_initialization() {
        let mut slice = [MaybeUninit::uninit(); 32];
        let buffer = Buffer::from_uninit_slice_mut(&mut slice);
        let initialized = buffer.init_by_filling(42);
        assert!(initialized.iter().all(|&byte| byte == 42));
    }
    #[test]
    fn buffer_parts() {
        let mut slice = [MaybeUninit::uninit(); 32];
        let mut buffer = Buffer::from_uninit_slice_mut(&mut slice);

        assert_eq!(buffer.uninit_part().len(), 32);
        assert_eq!(buffer.uninit_part_mut().len(), 32);
        assert_eq!(buffer.init_part(), &[]);
        assert_eq!(buffer.init_part_mut(), &mut []);
        assert!(!buffer.is_partially_filled());
        assert!(!buffer.is_completely_filled());
    }
}
