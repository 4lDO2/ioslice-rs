use core::mem::MaybeUninit;

use crate::Initialize;

/// An initialized tracking a container type that dereferences into a slice of
/// possibly-uninitialized bytes, and how many bytes have been initialized, respectively. The inner
/// data can always be moved out as uninitialized, but when the buffer _has_ been fully
/// initialized, the buffer can be turned into the initialized equivalent.
pub struct BufferInitializer<T> {
    // This is the Buffer type, that wraps a _single_ buffer that is not guaranteed to be fully
    // initialized when wrapped.
    //
    // The inner data, which must implement `Initialize` to do anything useful with points to a
    // slice of possibly uninitialized bytes, and must always return the same slice in the trait
    // (which is an unsafe trait implementation contract).
    pub(crate) inner: T,
    // Then we also have the initialization cursor, which marks the start of the uninitialized
    // region. This is unrelated to the number of bytes filled into the buffer, but it must always
    // be greater than or equal that.
    //
    // If this buffer is constructed from an already initialized slice, then this will be set to
    // the total capacity of the buffer. This cursor can never be decreased, and it must be less
    // than or equal to the total capacity.
    //
    // This allows dividing the buffer into an initialized region, and an uninitialized region.
    pub(crate) bytes_initialized: usize,

    // NOTE: If any of these contracts are broken inside the struct, expect UB. The
    // _`debug_assert_valid_len`_ method will check this everywhere when debug assertions are
    // enabled.
}

impl<T> BufferInitializer<T> {
    /// Wrap a possibly-uninitialized buffer into the initializer, with the current initialization
    /// cursor set to zero.
    #[inline]
    pub const fn uninit(inner: T) -> Self {
        Self {
            inner,
            bytes_initialized: 0,
        }
    }

    #[inline]
    pub const fn into_inner(self) -> T {
        self.inner
    }

    #[inline]
    pub const fn bytes_initialized(&self) -> usize {
        self.bytes_initialized
    }
}
impl<T> BufferInitializer<T>
where
    T: Initialize,
{
    pub(crate) fn debug_assert_validity(&self) {
        debug_assert!(self.bytes_initialized <= self.capacity());
    }

    #[inline]
    pub unsafe fn advance(&mut self, count: usize) {
        self.bytes_initialized = self.bytes_initialized.wrapping_add(count);
    }
    #[inline]
    pub unsafe fn advance_to_end(&mut self) {
        self.bytes_initialized = self.all_uninit().len();
    }

    #[inline]
    pub unsafe fn assume_init(self) -> T::Initialized {
        self.inner.assume_init()
    }

    #[inline]
    pub fn into_raw_parts(self) -> (T, usize) {
        let Self { inner, bytes_initialized } = self;
        (inner, bytes_initialized)
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
        self.inner.as_maybe_uninit_slice_mut()
    }
    /// Get the total size of the buffer that is being initialized.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.all_uninit().len()
    }
    #[inline]
    pub fn remaining(&self) -> usize {
        self.capacity().wrapping_sub(self.bytes_initialized)
    }
    /// Get the number of bytes that must be filled before the buffer gets fully initialized, and
    /// can be turned into an initialized type (e.g. `Box<[u8]>`).
    #[inline]
    pub fn bytes_to_init(&self) -> usize {
        debug_assert!(self.capacity() >= self.bytes_initialized);
        self.capacity().wrapping_sub(self.bytes_initialized)
    }
    /// Check whether the buffer is completely initialized. Note that this is unrelated to it being
    /// filled.
    #[inline]
    pub fn is_completely_init(&self) -> bool {
        self.bytes_initialized() == self.capacity()
    }
    /// Check whether no single byte of the buffer has been initialized.
    #[inline]
    pub fn is_completely_uninit(&self) -> bool {
        self.bytes_initialized() == 0
    }
    /// Retrieve a shared reference to the uninitialized part of the buffer. This is only included
    /// for completeness, since apart from some corner cases where one does not have exclusive
    /// access to the buffer but still wants to initialize it, is rather useless.
    #[inline]
    pub fn uninit_part(&self) -> &[MaybeUninit<u8>] {
        let all = self.all_uninit();

        // Validate that bytes_filled is valid, when _debug assertions_ are enabled.
        self.debug_assert_validity();

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
    /// Retrieve a shared slice to the initialized part of the buffer. Note that this is different
    /// from the _filled_ part, as a buffer can be fully initialized but not filled.
    #[inline]
    pub fn init_part(&self) -> &[u8] {
        // Validate that bytes_filled is valid, when _debug assertions_ are enabled.
        self.debug_assert_validity();

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

    /// Get a mutable slice to the uninitialized part of the buffer. Note that this is different
    /// from the unfilled part of it.
    #[inline]
    pub fn uninit_part_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        // NOTE: We extract pointers to avoid multiple mutable aliases when invoking
        // core::slice::from_raw_parts_mut.
        let (orig_ptr, orig_len) = unsafe {
            let orig = self.all_uninit_mut();
            (orig.as_mut_ptr(), orig.len())
        };
        unsafe {
            // Validate that bytes_filled is correct when debug assertions are enabled.
            self.debug_assert_validity();

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

    /// Retrieve a mutable slice to the initialized part of the buffer. Note that this is not the
    /// same as the filled part.
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
    /// Try to transform the initializing type, into its initialized counterpart, provided that the
    /// it has been fully initialized.
    #[inline]
    pub fn try_into_init(self) -> Result<T::Initialized, Self> {
        if self.is_completely_init() {
            Ok(unsafe { self.assume_init() })
        } else {
            Err(self)
        }
    }
    /// Finish the initialization by writing `byte` to the uninitialized region, and then get the
    /// final initialized type.
    pub fn finish_init_by_filling(self, byte: u8) -> T::Initialized {
        self.fill_uninit_part(byte);
        unsafe { self.assume_init() }
    }
    /// Finish the initialization by zeroing uninitialized region, and then get the final
    /// initialized type.
    pub fn finish_init_by_zeroing(self) -> T::Initialized {
        self.finish_init_by_filling(0_u8)
    }
    /// Fill the uninitialized part with copies of `byte` (memset).
    ///
    /// After this method has been called, it is safe to [`assume_init`]. [`try_into_init`] will
    /// then also succeed.
    #[inline]
    pub fn fill_uninit_part(&mut self, byte: u8) -> &mut [u8] {
        crate::fill_uninit_slice(self.uninit_part_mut(), byte)
    }
    /// Zero the uninitialized part.
    ///
    /// After this method has been called, it is safe to [`assume_init`]. [`try_into_init`] will
    /// then also succeed.
    #[inline]
    pub fn uninit_part_zeroed(&mut self) -> &mut [u8] {
        self.fill_uninit_part(0_u8)
    }
    /// Get both the initialized and uninitialized parts simultaneously. This method is nothing but
    /// a shorthand for the individual methods, but included for completeness.
    ///
    /// This is because the mutable counterpart [`init_uninit_parts_mut`] cannot be done separately
    /// by calling the [`init_part_mut`] and [`uninit_part_mut`] methods.
    #[inline]
    pub fn init_uninit_parts(&self) -> (&[u8], &[MaybeUninit<u8>]) {
        (self.init_part(), self.uninit_part())
    }
    /// Borrow both the initialized as well as the uninitialized parts, mutably.
    #[inline]
    pub fn init_uninit_parts_mut(&mut self) -> (&mut [u8], &mut [MaybeUninit<u8>]) {
        let (all_ptr, all_len) = unsafe {
            let all = self.all_uninit_mut();

            (all.as_mut_ptr(), all.len())
        };

        unsafe {
            self.debug_assert_validity();

            let init_base_ptr = all_ptr as *mut u8;
            let init_len = self.bytes_initialized;

            let uninit_base_ptr = all_ptr.add(self.bytes_initialized);
            let uninit_len = all_len.wrapping_sub(self.bytes_initialized);

            let init = core::slice::from_raw_parts_mut(init_base_ptr, init_len);
            let uninit = core::slice::from_raw_parts_mut(uninit_base_ptr, uninit_len);
            
            (init, uninit)
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_initialization() {
        let mut slice = [MaybeUninit::uninit(); 32];
        let buffer = BufferInitializer::uninit(&mut slice[..]);
        let initialized = buffer.finish_init_by_filling(42_u8);
        assert!(initialized.iter().all(|&byte| byte == 42_u8));
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