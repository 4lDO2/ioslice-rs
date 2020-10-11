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
        buf.uninit_part_mut().init_by_filling(self.byte());

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

pub struct Buffer<T> {
    inner: T,
    // TODO: Use a trait to omit this field when the type already is initialized.
    // NOTE: We use this counter __only internally__. Namely, in order to avoid unnecessary bounds
    // checking when indexing buffers, this must not be changed to any arbitrary value.
    bytes_filled: usize,
}
pub struct BufferRef<'buffer, T> {
    buffer: &'buffer mut Buffer<T>,
}

impl<T> Buffer<T> {
    #[inline]
    pub const fn new(inner: T) -> Self {
        Self {
            inner,
            bytes_filled: 0,
        }
    }
    #[inline]
    pub fn into_inner(self) -> T {
        self.inner
    }

    #[inline]
    pub fn bytes_filled(&self) -> usize {
        self.bytes_filled
    }

    #[inline]
    pub fn by_ref<'buffer>(&'buffer mut self) -> BufferRef<'buffer, T> {
        BufferRef {
            buffer: self,
        }
    }
}

impl<T> Buffer<T>
where
    T: InitializeIndirect,
{
    fn debug_assert_valid_len(&self) {
        debug_assert!(self.all_uninit().len() >= self.bytes_filled);
        debug_assert!(self.bytes_filled <= isize::MAX as usize);
    }

    #[inline]
    pub fn all_uninit(&self) -> &[MaybeUninit<u8>] {
        self.inner.as_maybe_uninit_slice()
    }
    #[inline]
    pub fn bytes_to_fill(&self) -> usize {
        self.debug_assert_valid_len();

        self.all_uninit().len().wrapping_sub(self.bytes_filled)
    }
    #[inline]
    pub fn is_completely_filled(&self) -> bool {
        self.bytes_to_fill() == 0
    }
    #[inline]
    pub fn is_partially_filled(&self) -> bool {
        self.bytes_filled() > 0
    }
    #[inline]
    pub fn try_full_initialized(&self) -> Option<&[u8]> {
        if self.is_completely_filled() {
            Some(self.init_part())
        } else {
            None
        }
    }
    #[inline]
    pub fn uninit_part(&self) -> &[MaybeUninit<u8>] {
        let all = self.all_uninit();
        dbg!(all.len());
        dbg!(self.bytes_filled);

        // NOTE: We use unsafe to eliminate unnecessary bounds checking. This may be negligible for
        // many scenarios, but we want to keep this interface zero-cost.
        unsafe {
            // Validate that bytes_filled is valid, when _debug assertions_ are enabled.
            self.debug_assert_valid_len();

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
            let ptr = all.as_ptr().add(self.bytes_filled);
            let len = all.len().wrapping_sub(self.bytes_filled);

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
        let all = self.all_uninit();

        // NOTE: Use of unsafe is only to eliminate bounds checks and maintain zero-cost.
        unsafe {
            // Validate that bytes_filled is valid, when _debug assertions_ are enabled.
            self.debug_assert_valid_len();

            let ptr = all.as_ptr();
            let len = self.bytes_filled;

            // SAFETY: This is safe, due to the same invariants as with `uninit_part`, except for
            // the initialization invariant. We uphold this, by guaranteeing that the entire slice
            // we construct, is initialized, since this is a contract merely from using this
            // wrapper. We also uphold the validity variant, which is somewhat different in this
            // case, since we know that bytes_filled must be smaller than or equal to the size of
            // the slice.
            core::slice::from_raw_parts(ptr as *const u8, len)
        }
    }
    #[inline]
    fn all_uninit_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.inner.as_maybe_uninit_slice_mut()
    }

    #[inline]
    pub fn uninit_part_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        // NOTE: We extract this to avoid multiple mutable aliases.
        let (orig_ptr, orig_len) = {
            let all = self.all_uninit_mut();

            (all.as_mut_ptr(), all.len())
        };

        unsafe {
            // Validate that bytes_filled is correct when debug assertions are enabled.
            self.debug_assert_valid_len();

            // SAFETY: This pointer arithmetic operation, is safe for the same reasons as with
            // `uninit_part`.
            let ptr = orig_ptr.add(self.bytes_filled);

            let len = orig_len.wrapping_sub(self.bytes_filled);

            // SAFETY: This is safe for the exact same reasons as with `uninit_part`, but that
            // there must not be any reference _at all_ to the inner slice. This is upheld by
            // knowing that we have already borrowed the owner of the slice mutably.
            core::slice::from_raw_parts_mut(ptr, len)
        }
    }

    #[inline]
    pub fn init_part_mut(&mut self) -> &mut [u8] {
        // NOTE: We extract pointer+len in a separate block, to avoid creating multiple mutable
        // references to the same data.
        let orig_ptr = {
            let all = self.all_uninit_mut();
            all.as_mut_ptr()
        };

        unsafe {
            let ptr = orig_ptr;
            let len = self.bytes_filled;

            // SAFETY: This is safe for the exact same reasons as with `init_part`, except that we
            // also ensure that there is no access whatsoever to the inner data, since we are
            // borrowing `self` mutably.
            core::slice::from_raw_parts_mut(ptr as *mut u8, len)
        }
    }
    /// Advance the internal cursor, that divides the initialized and uninitialized parts.
    ///
    /// # Safety
    ///
    /// For this to be safe, the following safety invariants must be upheld:
    ///
    /// * `count` must not overflow the size of the full slice (which in turn must not overflow the
    ///   size of `isize::MAX`);
    /// * at least `count` consecutive bytes of the uninitialized part, must have been written to.
    ///
    /// # Panics
    ///
    /// This will panic rather than causing UB, when _debug assertions_ are enabled. That is, it
    /// will panic if the count, when added with the current number of bytes filled, neither
    /// overflows `isize::MAX`, nor the total size of the slice.
    #[inline]
    pub unsafe fn advance(&mut self, count: usize) {
        debug_assert!(self.bytes_filled.checked_add(count).map_or(false, |sum| sum <= isize::MAX as usize));

        if count > isize::MAX as usize {
            core::hint::unreachable_unchecked();
        }
        self.bytes_filled = self.bytes_filled.wrapping_add(count);

        self.debug_assert_valid_len();
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
    pub unsafe fn advance_to_end(&mut self) {
        self.bytes_filled = self.uninit_part().len();
    }
    /// Assume that the entire buffer has been initialized, returning the inner initialized type.
    ///
    /// # Safety
    ///
    /// This is unsafe since it must uphold the initialization invariant; every byte of the
    /// uninitialized part must have been written to.
    #[inline]
    pub unsafe fn assume_init(self) -> T::InitializedSlice {
        self.inner.assume_init_all()
    }
    /// Revert the internal cursor to 0, forgetting about the initialized bytes.
    #[inline]
    pub fn revert_to_start(&mut self) {
        self.bytes_filled = 0;
    }
    pub fn fill_from_source(&mut self, mut source: impl Source) {
        source.fill(self.by_ref())
    }
    #[inline]
    pub fn try_into_init(self) -> Result<T::InitializedSlice, Self> {
        if self.is_completely_filled() {
            Ok(unsafe { self.assume_init() })
        } else {
            Err(self)
        }
    }
    pub fn try_init_from_source(mut self, source: impl Source) -> Result<T::InitializedSlice, Self> {
        self.fill_from_source(source);
        self.try_into_init()
    }
    pub fn init_from_source(mut self, source: impl Source + FullSource) -> T::InitializedSlice {
        self.fill_from_source(source);

        match self.try_into_init() {
            Ok(t) => t,
            Err(_) => unreachable!("trait contract broken: FullSource impl must guarantee that all buffers are fully initialized"),
        }
    }
    // TODO: Use specialization to merge init_from_source and init_from_trusted_source into a
    // single function.
    pub fn init_from_trusted_source(mut self, source: impl Source + TrustedFullSource) -> T::InitializedSlice {
        self.fill_from_source(source);

        unsafe { self.assume_init() }
    }
    pub fn init_by_filling(self, byte: u8) -> T::InitializedSlice {
        self.init_from_trusted_source(Fill::from_byte(byte))
    }
    pub fn init_by_zeroing(self) -> T::InitializedSlice {
        self.init_by_filling(0_u8)
    }
}

impl<'a> Buffer<&'a mut [u8]> {
    #[inline]
    pub fn from_slice_mut(slice: &'a mut [u8]) -> Self {
        Self {
            bytes_filled: slice.len(),
            inner: slice,
        }
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
        self.buffer.bytes_filled()
    }

    #[inline]
    pub fn by_ref<'shorter>(&'shorter mut self) -> BufferRef<'shorter, T> {
        BufferRef {
            buffer: self.buffer,
        }
    }
}

impl<'buffer, T> BufferRef<'buffer, T>
where
    T: InitializeIndirect,
{
    #[inline]
    pub fn all_uninit(&self) -> &[MaybeUninit<u8>] {
        self.buffer.all_uninit()
    }
    #[inline]
    pub fn bytes_to_fill(&self) -> usize {
        self.buffer.bytes_to_fill()
    }
    #[inline]
    pub fn uninit_part(&self) -> &[MaybeUninit<u8>] {
        self.buffer.uninit_part()
    }
    #[inline]
    pub fn init_part(&self) -> &[u8] {
        self.buffer.init_part()
    }
    #[inline]
    pub fn all_uninit_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.buffer.all_uninit_mut()
    }
    #[inline]
    pub fn uninit_part_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.buffer.uninit_part_mut()
    }
    #[inline]
    pub fn init_part_mut(&mut self) -> &mut [u8] {
        self.buffer.init_part_mut()
    }
    #[inline]
    pub unsafe fn advance(&mut self, count: usize) {
        self.buffer.advance(count)
    }
    #[inline]
    pub unsafe fn advance_to_end(&mut self) {
        self.buffer.advance_to_end()
    }
    #[inline]
    pub fn revert_to_start(&mut self) {
        self.buffer.revert_to_start()
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
