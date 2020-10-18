use core::mem::MaybeUninit;

use crate::{Initialize, InitializeIndirect};

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

    /// Retrieve the current buffer immutably, provided that there is one.
    #[inline]
    pub fn current_buffer(&self) -> Option<&[MaybeUninit<u8>]> {
        Some(self.all_vectors_uninit().get(self.vectors_filled)?.as_maybe_uninit_slice())
    }
    /// Retrieve the current buffer mutably, provided that there is one.
    pub unsafe fn current_buffer_mut(&mut self) -> Option<&mut [MaybeUninit<u8>]> {
        Some(self.all_vectors_uninit_mut().get_mut(self.vectors_filled)?.as_maybe_uninit_slice_mut())
    }
    fn debug_assert_validity(&self) {
        debug_assert!(self.current_buffer().map_or(true, |current_buffer| current_buffer.len() >= self.bytes_filled_for_vector));
        debug_assert!(self.bytes_filled_for_vector <= isize::MAX as usize);
        debug_assert!(self.inner.as_maybe_uninit_slices().len() >= self.vectors_filled);
    }

    /// Get the total number of vectors, since the wrapper was constructed.
    #[inline]
    pub fn total_vector_count(&self) -> usize {
        self.inner.as_maybe_uninit_slices().len()
    }

    /// Get the number of vectors that are currently filled and completely initialized.
    #[inline]
    pub fn vectors_filled(&self) -> usize {
        self.vectors_filled
    }

    /// Get the number of vectors remaining, possibly including the vector that is currently
    /// initializing.
    #[inline]
    pub fn vectors_remaining(&self) -> usize {
        self.total_vector_count().wrapping_sub(self.vectors_filled())
    }

    /// Counts the bytes that must be filled before the whole buffer is initialized.
    ///
    /// Note that this can be expensive if there are many buffers; it is O(n), where `n` is the
    /// number of vectors. If all vectors are already filled, then this completes in constant time.
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

