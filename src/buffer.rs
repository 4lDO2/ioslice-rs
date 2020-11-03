//! Buffers for single-buffer and vectored I/O which tracking initializedness and how much has been
//! filled. Container types pointing to possibly-uninitialized memory such as
//! `Vec<MaybeUninit<u8>>`, `IoBox<Uninitialized>`, or `Box<[MaybeUninit<u8>]> can be transformed
//! into their initialized variants via the [`Initialize`] trait, within requiring unsafe code.
//!
//! This is an implementation of an API similar to what has been proposed in [this
//! RFC](https://github.com/sfackler/rfcs/blob/read-buf/text/0000-read-buf.md).

use core::mem::MaybeUninit;

use crate::{Initialize, InitializeExt};

use crate::initializer::BufferInitializer;

pub struct Buffer<T> {
    initializer: BufferInitializer<T>,
    bytes_filled: usize,
}

/// A reference to a [`Buffer`], which is meant be a subset of the functionality offered by the
/// fully owned buffer.
///
/// For example, it neither allows reading from the unfilled region, nor swapping out the buffer
/// pointed to, with anything else.
pub struct BufferRef<'buffer, T> {
    // NOTE: The reference here is private, and never accessed using the API, _since we don't want
    // an API user to be able to replace a `&mut Buffer` with a completely different one_.
    inner: &'buffer mut Buffer<T>,
}

impl<T> Buffer<T> {
    /// Create a new buffer from an initializer.
    #[inline]
    pub const fn from_initializer(initializer: BufferInitializer<T>) -> Self {
        Self {
            initializer,
            bytes_filled: 0,
        }
    }
    /// Create a new buffer, defaulting to not being initialized, nor filled. Prefer [`new_init`]
    /// if the buffer is already initialized.
    pub const fn uninit(inner: T) -> Self {
        Self::from_initializer(BufferInitializer::uninit(inner))
    }
    /// Move out the buffer initializer, which contains the inner buffer and initialization cursor,
    /// and get the filledness cursor.
    #[inline]
    pub fn into_raw_parts(self) -> (BufferInitializer<T>, usize) {
        let Self {
            initializer,
            bytes_filled,
        } = self;

        (initializer, bytes_filled)
    }
    /// Move out the inner buffer, being uninitialized or initialized based on whatever it was when
    /// this buffer was constructed.
    ///
    /// Use [`try_into_init`] if the buffer is initialized.
    #[inline]
    pub fn into_inner(self) -> T {
        self.initializer.into_inner()
    }

    /// Get the number of bytes that are currently filled, within the buffer. Note that this is
    /// different from the number of initialized bytes; use [`bytes_initialized`] for that.
    #[inline]
    pub const fn bytes_filled(&self) -> usize {
        self.bytes_filled
    }

    #[inline]
    pub fn by_ref<'buffer>(&'buffer mut self) -> BufferRef<'buffer, T> {
        BufferRef { inner: self }
    }

    #[inline]
    pub const fn initializer(&self) -> &BufferInitializer<T> {
        &self.initializer
    }

    #[inline]
    pub fn initializer_mut(&mut self) -> &mut BufferInitializer<T> {
        &mut self.initializer
    }
}

impl<T> Buffer<T>
where
    T: Initialize,
{
    #[inline]
    pub fn capacity(&self) -> usize {
        self.initializer.capacity()
    }

    pub(crate) fn debug_assert_validity(&self) {
        self.initializer.debug_assert_validity();
        debug_assert!(self.bytes_filled() <= self.capacity());
        debug_assert!(self.bytes_filled() <= self.initializer.bytes_initialized());
    }
    /// Get the number of bytes that may be filled before the buffer is full.
    #[inline]
    pub fn remaining(&self) -> usize {
        debug_assert!(self.capacity() >= self.bytes_filled);
        self.capacity().wrapping_sub(self.bytes_filled)
    }
    /// Check whether the buffer is completely filled, and thus also initialized.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.bytes_filled() == self.capacity()
    }
    /// Check whether the buffer is empty. It can be partially or fully initialized however.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.bytes_filled() == 0
    }
    /// Retrieve a shared slice to the filled part of the buffer.
    #[inline]
    pub fn filled_part(&self) -> &[u8] {
        unsafe {
            self.debug_assert_validity();

            let ptr = self.initializer.all_uninit().as_ptr();
            let len = self.bytes_filled;

            core::slice::from_raw_parts(ptr as *const u8, len)
        }
    }
    /// Retrieve a mutable slice to the filled part of the buffer.
    #[inline]
    pub fn filled_part_mut(&mut self) -> &mut [u8] {
        let orig_ptr = unsafe { self.initializer.all_uninit_mut().as_mut_ptr() };

        unsafe {
            self.debug_assert_validity();

            let ptr = orig_ptr;
            let len = self.bytes_filled;

            core::slice::from_raw_parts_mut(ptr as *mut u8, len)
        }
    }
    /// Get a shared slice to the unfilled part, which may be uninitialized.
    #[inline]
    pub fn unfilled_part(&self) -> &[MaybeUninit<u8>] {
        let (orig_ptr, orig_len) = {
            let orig = self.initializer.all_uninit();

            (orig.as_ptr(), orig.len())
        };

        unsafe {
            self.debug_assert_validity();

            let ptr = orig_ptr.add(self.bytes_filled);
            let len = orig_len.wrapping_sub(self.bytes_filled);

            core::slice::from_raw_parts(ptr, len)
        }
    }
    /// Get a mutable reference to the unfilled part of the buffer, which may overlap with the
    /// initialized-but-nonfilled region.
    ///
    /// # Safety
    ///
    /// Due to the possibility of an overlap between the part that is initialized and the part that
    /// is unfilled, the caller must ensure that the resulting slice is never used to deinitialize
    /// the buffer.
    ///
    /// It is thus recommended to use [`append`] or [`fill`] instead, since those are the by far
    /// most common operations to do when initializing. However, code that requires interfacing
    /// with other APIs such as system calls, need to use this function.
    ///
    /// If mutable access really is needed for the unfilled region in safe code, consider using
    /// [`unfilled_init_uninit_parts_mut`].
    #[inline]
    pub unsafe fn unfilled_part_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        let (orig_ptr, orig_len) = {
            let orig = self.initializer.all_uninit_mut();
            (orig.as_mut_ptr(), orig.len())
        };

        self.debug_assert_validity();

        let ptr = orig_ptr.add(self.bytes_filled);
        let len = orig_len.wrapping_sub(self.bytes_filled);

        core::slice::from_raw_parts_mut(ptr, len)
    }
    /// Borrow both the filled and unfilled parts immutably.
    #[inline]
    pub fn filled_unfilled_parts(&self) -> (&[u8], &[MaybeUninit<u8>]) {
        (self.filled_part(), self.unfilled_part())
    }
    /// Borrow the filled part, the unfilled but initialized part, and the unfilled and
    /// uninitialized part.
    #[inline]
    pub fn all_parts(&self) -> (&[u8], &[u8], &[MaybeUninit<u8>]) {
        (
            self.filled_part(),
            self.unfilled_init_part(),
            self.unfilled_uninit_part(),
        )
    }

    #[inline]
    pub fn all_parts_mut(&mut self) -> (&mut [u8], &mut [u8], &mut [MaybeUninit<u8>]) {
        let (all_ptr, all_len) = unsafe {
            let all = self.initializer.all_uninit_mut();

            (all.as_mut_ptr(), all.len())
        };

        unsafe {
            self.debug_assert_validity();

            let filled_base_ptr = all_ptr as *mut u8;
            let filled_len = self.bytes_filled;

            let unfilled_init_base_ptr = all_ptr.add(self.bytes_filled) as *mut u8;
            let unfilled_init_len = self
                .initializer
                .bytes_initialized()
                .wrapping_sub(self.bytes_filled);

            let unfilled_uninit_base_ptr = all_ptr.add(self.initializer.bytes_initialized());
            let unfilled_uninit_len = all_len.wrapping_sub(self.initializer.bytes_initialized());

            let filled = core::slice::from_raw_parts_mut(filled_base_ptr, filled_len);
            let unfilled_init =
                core::slice::from_raw_parts_mut(unfilled_init_base_ptr, unfilled_init_len);
            let unfilled_uninit =
                core::slice::from_raw_parts_mut(unfilled_uninit_base_ptr, unfilled_uninit_len);

            (filled, unfilled_init, unfilled_uninit)
        }
    }

    /// Borrow both the filled and the unfilled parts, mutably.
    ///
    /// # Safety
    ///
    /// This is unsafe as the uninit part may have bytes in it that are tracked to be initialized.
    /// It is hence the responsibility of the caller to ensure that the buffer is not deinitialized
    /// by writing [`MaybeUninit::uninit()`] to it.
    #[inline]
    pub unsafe fn filled_unfilled_parts_mut(&mut self) -> (&mut [u8], &mut [MaybeUninit<u8>]) {
        let (all_ptr, all_len) = {
            let all = self.initializer.all_uninit_mut();

            (all.as_mut_ptr(), all.len())
        };

        {
            self.debug_assert_validity();

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
    pub fn unfilled_init_part(&self) -> &[u8] {
        unsafe {
            self.debug_assert_validity();

            let all = self.initializer.all_uninit();
            let all_ptr = all.as_ptr();

            let unfilled_init_base_ptr = all_ptr.add(self.bytes_filled) as *const u8;
            let unfilled_init_len = self
                .initializer
                .bytes_initialized()
                .wrapping_sub(self.bytes_filled);

            core::slice::from_raw_parts(unfilled_init_base_ptr, unfilled_init_len)
        }
    }

    /// Get the initialized part of the unfilled part, if there is any.
    #[inline]
    pub fn unfilled_init_part_mut(&mut self) -> &mut [u8] {
        let (_, unfilled_init, _) = self.all_parts_mut();

        unfilled_init
    }
    #[inline]
    pub fn unfilled_uninit_part(&self) -> &[MaybeUninit<u8>] {
        self.initializer.uninit_part()
    }
    /// Get the uninitialized part of the unfilled part, if there is any.
    #[inline]
    pub fn unfilled_uninit_part_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.initializer.uninit_part_mut()
    }

    #[inline]
    pub fn unfilled_parts(&mut self) -> (&[u8], &[MaybeUninit<u8>]) {
        let (_, init, uninit) = self.all_parts();

        (init, uninit)
    }
    #[inline]
    pub fn unfilled_parts_mut(&mut self) -> (&mut [u8], &mut [MaybeUninit<u8>]) {
        let (_, init, uninit) = self.all_parts_mut();

        (init, uninit)
    }

    /// Revert the internal cursor to 0, forgetting about the initialized bytes.
    #[inline]
    pub fn revert_to_start(&mut self) {
        self.by_ref().revert_to_start()
    }
    #[inline]
    pub fn append(&mut self, slice: &[u8]) {
        // TODO: If this would ever turn out to be worth it, this could be optimized as bounds
        // checking gets redundant here.
        let unfilled_part = unsafe { self.unfilled_part_mut() };
        assert!(slice.len() <= unfilled_part.len());
        unfilled_part[..slice.len()].copy_from_slice(crate::cast_init_to_uninit_slice(slice));
    }
    #[inline]
    pub fn advance(&mut self, count: usize) {
        assert!(
            self.initializer
                .bytes_initialized()
                .wrapping_sub(self.bytes_filled)
                >= count,
            "advancing filledness cursor beyond the initialized region"
        );
        self.bytes_filled = self.bytes_filled.wrapping_add(count);
    }
    pub unsafe fn assume_init(&mut self, count: usize) {
        self.bytes_filled = self.bytes_filled.wrapping_add(count);
        self.initializer.bytes_initialized =
            core::cmp::min(self.bytes_filled, self.initializer.bytes_initialized);

        self.debug_assert_validity();
    }
    pub unsafe fn assume_init_all(&mut self) {
        self.bytes_filled = self.capacity();
        self.initializer.bytes_initialized = self.capacity();
    }
    #[inline]
    pub fn fill_by_repeating(&mut self, byte: u8) {
        unsafe {
            self.unfilled_part_mut().init_by_filling(byte);
        }
    }
    #[inline]
    pub fn fill_by_zeroing(&mut self) {
        unsafe {
            self.unfilled_part_mut().init_by_zeroing();
        }
    }
}
impl<'a> Buffer<&'a mut [u8]> {
    // TODO: Use a trait that makes the dynamic counter statically set to full.
    #[inline]
    pub fn from_slice_mut(slice: &'a mut [u8]) -> Self {
        let mut initializer = BufferInitializer::uninit(slice);
        unsafe {
            initializer.advance_to_end();
        }
        Self::from_initializer(initializer)
    }
}
impl<'a> Buffer<&'a mut [MaybeUninit<u8>]> {
    #[inline]
    pub fn from_uninit_slice_mut(slice: &'a mut [MaybeUninit<u8>]) -> Self {
        Self::uninit(slice)
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
        BufferRef { inner: self.inner }
    }
}

impl<'buffer, T> BufferRef<'buffer, T>
where
    T: Initialize,
{
    #[inline]
    pub fn remaining(&self) -> usize {
        self.inner.remaining()
    }
    #[inline]
    pub fn unfilled_parts(&mut self) -> (&mut [u8], &mut [MaybeUninit<u8>]) {
        self.inner.unfilled_parts_mut()
    }
    #[inline]
    pub unsafe fn unfilled_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.inner.unfilled_part_mut()
    }
    #[inline]
    pub unsafe fn advance(&mut self, count: usize) {
        self.inner.assume_init(count)
    }
    #[inline]
    pub unsafe fn advance_all(&mut self) {
        self.inner.assume_init_all();
    }
    #[inline]
    pub fn revert_to_start(&mut self) {
        self.inner.revert_to_start()
    }
    #[inline]
    pub fn fill_by_repeating(&mut self, byte: u8) {
        self.inner.fill_by_repeating(byte)
    }
    #[inline]
    pub fn fill_by_zeroing(&mut self) {
        self.inner.fill_by_zeroing()
    }
}

#[cfg(test)]
mod tests {
    //use super::*;
}
