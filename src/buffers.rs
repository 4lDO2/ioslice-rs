use core::mem::MaybeUninit;

use crate::{Initialize, InitializeVectored};
use crate::initializer::BuffersInitializer;

pub struct Buffers<T> {
    initializer: BuffersInitializer<T>,
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

impl<T> Buffers<T> {
    #[inline]
    pub const fn from_initializer(initializer: BuffersInitializer<T>) -> Self {
        Self {
            initializer,
            bytes_filled_for_vector: 0,
            vectors_filled: 0,
        }
    }
    #[inline]
    pub const fn new(inner: T) -> Self {
        Self::from_initializer(BuffersInitializer::uninit(inner))
    }
    #[inline]
    pub const fn initializer(&self) -> &BuffersInitializer<T> {
        &self.initializer
    }
    #[inline]
    pub fn initializer_mut(&mut self) -> &mut BuffersInitializer<T> {
        &mut self.initializer
    }
    #[inline]
    pub fn into_initializer(self) -> BuffersInitializer<T> {
        let Self { initializer, .. } = self;

        initializer
    }
    #[inline]
    pub fn into_inner(self) -> T {
        self.into_initializer().into_inner()
    }
    #[inline]
    pub const fn vectors_filled(&self) -> usize {
        self.vectors_filled
    }
}
impl<T> Buffers<T>
where
    T: InitializeVectored,
{
    #[inline]
    pub fn all_previously_filled_vectors(&self) -> &[crate::Init<T::UninitVector>] {
        self.debug_assert_validity();

        unsafe {
            let filled = {
                let src = self.initializer().all_uninit_vectors();

                core::slice::from_raw_parts(src.as_ptr(), self.vectors_filled())
            };

            crate::Init::from_slices(filled)
        }
    }
    #[inline]
    pub fn all_previously_filled_vectors_mut(&self) -> &[crate::Init<T::UninitVector>] {
        self.debug_assert_validity();

        unsafe {
            let ptr = {
                self.initializer_mut().all_uninit_vectors_mut().as_mut_ptr()
            };
            let filled = core::slice::from_raw_parts_mut(ptr, self.vectors_filled());
            crate::Init::from_slices_mut(filled)
        }
    }
    #[inline]
    pub fn current_vector_all(&self) -> Option<&[MaybeUninit<u8>]> {
        self.debug_assert_validity();

        let all_vectors = self.initializer().all_uninit_vectors();

        if self.vectors_filled == all_vectors.len() {
            None
        } else {
            Some(unsafe { all_vectors.get_unchecked(self.vectors_filled) }.as_maybe_uninit_slice())
        }
    }
    #[inline]
    pub unsafe fn current_vector_all_mut(&mut self) -> Option<&mut [MaybeUninit<u8>]> {
        self.debug_assert_validity();

        let all_vectors_mut = self.initializer().all_uninit_vectors_mut();

        if self.vectors_filled == all_vectors_mut.len() {
            None
        } else {
            Some(all_vectors_mut.get_unchecked_mut(self.vectors_filled).as_maybe_uninit_slice_mut())
        }
    }
    #[inline]
    pub fn current_vector_init_uninit_parts(&self) -> Option<(&[u8], &[MaybeUninit<u8>])> {
        self.debug_assert_validity();

        let ordering = self.vectors_filled().cmp(&self.initializer().vectors_initialized());

        match ordering {
            // The current vector is filled, but there are one or more vectors in front of it, that
            // are already initialized. We can thus simply assume that the current vector is
            // completely initialized.
            core::cmp::Ordering::Less => Some((unsafe { crate::cast_uninit_to_init_slice(self.current_vector_all()?) }, &[])),

            // The current vector (when tracking how they're filled) is behind one in front of it
            // that is not yet initialized. This cannot happen, and is library UB.
            core::cmp::Ordering::Greater => unsafe { core::hint::unreachable_unchecked() },

            // If the current vector is both in the initializing and in the filling phase, then we
            // will need to split it according to the initializer.
            core::cmp::Ordering::Equal => self.initializer().current_vector_init_uninit_parts(),
        }
    }
    #[inline]
    pub fn current_vector_init_uninit_parts_mut(&mut self) -> Option<(&mut [u8], &mut [MaybeUninit<u8>])> {
        self.debug_assert_validity();

        let ordering = self.vectors_filled().cmp(&self.initializer().vectors_initialized());

        match ordering {
            // NOTE: See current_vector_init_uninit_parts. I'm lazy and I don't strive to avoid
            // redundancy, except at the API level :-)
            core::cmp::Ordering::Less => Some((unsafe { crate::cast_uninit_to_init_slice_mut(self.current_vector_all_mut()?) }, &mut [])),
            core::cmp::Ordering::Greater => unsafe { core::hint::unreachable_unchecked() },
            core::cmp::Ordering::Equal => self.initializer().current_vector_init_uninit_parts_mut(),
        }
    }
    #[inline]
    pub fn current_vector_filled_part(&self) -> Option<&[u8]> {
        self.debug_assert_validity();

        let base_ptr = { self.current_vector_all()?.as_ptr() };

        Some(unsafe {
            core::slice::from_raw_parts(base_ptr as *const u8, self.bytes_filled_for_vector)
        })
    }
    #[inline]
    pub fn current_vector_filled_part_mut(&self) -> Option<&mut [u8]> {
        self.debug_assert_validity();

        unsafe {
            let base_ptr = { self.current_vector_all_mut()?.as_mut_ptr() };
            Some(core::slice::from_raw_parts_mut(base_ptr as *mut u8, self.bytes_filled_for_vector))
        }
    }
    #[inline]
    pub fn current_vector_unfilled_all_part(&self) -> Option<&[MaybeUninit<u8>]> {
        self.debug_assert_validity();

        let (base_ptr, base_len) = {
            let all = self.current_vector_all()?;
            (all.as_ptr(), all.len())
        };

        Some(unsafe {
            let ptr = base_ptr.add(self.bytes_filled_for_vector);
            let len = base_len - self.bytes_filled_for_vector;

            core::slice::from_raw_parts(ptr, len)
        })
    }
    #[inline]
    pub unsafe fn current_vector_unfilled_all_part_mut(&self) -> Option<&mut [MaybeUninit<u8>]> {
        self.debug_assert_validity();

        let (base_ptr, base_len) = {
            let all = self.current_vector_all_mut()?;
            (all.as_mut_ptr(), all.len())
        };

        Some({
            let ptr = base_ptr.add(self.bytes_filled_for_vector);
            let len = base_len - self.bytes_filled_for_vector;

            core::slice::from_raw_parts_mut(ptr, len)
        })
    }
    #[inline]
    pub fn all_next_unfilled_vectors(&self) -> &[T::UninitVector] {
        self.debug_assert_validity();

        let total_vector_count = self.total_vector_count();
        let vectors_filled = self.vectors_filled();
        let after_vectors_filled = vectors_filled + 1;

        let is_within = vectors_filled != total_vector_count && after_vectors_filled != total_vector_count;

        if is_within {
            unsafe {
                let (src_ptr, src_len) = {
                    let src = self.initializer().all_uninit_vectors();

                    (src.as_ptr(), src.len())
                };

                // SAFETY: See safe docs for all_next_unfilled_vectors_mut.
                let ptr = src_ptr.add(after_vectors_filled);
                let len = src_len - after_vectors_filled;

                core::slice::from_raw_parts(ptr, len)
            }
        } else {
            &[]
        }
    }
    #[inline]
    pub fn all_next_unfilled_vectors_mut(&mut self) -> &mut [T::UninitVector] {
        self.debug_assert_validity();

        let total_vector_count = self.total_vector_count();
        let vectors_filled = self.vectors_filled();
        let after_vectors_filled = vectors_filled + 1;

        let is_within = vectors_filled != total_vector_count && after_vectors_filled != total_vector_count;

        if is_within {
            unsafe {
                let (src_ptr, src_len) = {
                    let src = self.initializer().all_uninit_vectors_mut();

                    (src.as_mut_ptr(), src.len())
                };
                // SAFETY: Since the number of vectors filled can __never__ be larger than the total
                // number of vectors, we can assume that `vectors_filled + 1 < total_vector_count`,
                // means that it must be less. Therefore, it resides in the same allocated object
                // as the original slice, making ptr::add safe.
                let ptr = src_ptr.add(after_vectors_filled);
                let len = total_vector_count - after_vectors_filled;

                core::slice::from_raw_parts_mut(ptr, len)
            }
        } else {
            &mut []
        }
    }
    /// Return all vectors that have been fully filled, sequentially, as well as the filled part of
    /// the current vector.
    pub fn all_filled_vectors(&self) -> (&[crate::Init<T::UninitVector>], &[u8]) {
    }
    /// For the current vector, return the unfilled and initialized part, the unfilled but
    /// initialized part, and the unfilled and uninitialized part, in that order.
    pub fn current_vector_parts(&self) -> (&[u8], &[u8], &[MaybeUninit<u8>]) {
    }
    /// For the current vector, return the unfilled and initialized part, the unfilled but
    /// initialized part, and the unfilled and uninitialized part mutably, in that order.
    pub fn current_vector_parts_mut(&mut self) -> (&mut [u8], &mut [u8], &mut [MaybeUninit<u8>]) {
    }
    fn debug_assert_validity(&self) {
        debug_assert!(self.bytes_filled_for_vector <= isize::MAX as usize);
        debug_assert!(self.vectors_filled <= self.initializer().total_vector_count());
        // TODO
    }
    #[inline]
    pub fn total_vector_count(&self) -> usize {
        self.initializer().total_vector_count()
    }
    #[inline]
    pub fn vectors_remaining(&self) -> usize {
        self.total_vector_count().wrapping_sub(self.vectors_filled())
    }
    pub fn count_bytes_to_fill(&self) -> usize {
    }
    pub fn count_total_bytes_in_all_vectors(&self) -> usize {
        self.initializer().count_total_bytes_in_all_vectors()
    }
}
