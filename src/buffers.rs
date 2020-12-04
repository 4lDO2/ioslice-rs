use core::mem::MaybeUninit;

use crate::initializer::BuffersInitializer;
use crate::{Initialize, InitializeVectored};

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

            crate::Init::cast_from_slices(filled)
        }
    }
    #[inline]
    pub fn all_previously_filled_vectors_mut(&mut self) -> &[crate::Init<T::UninitVector>] {
        self.debug_assert_validity();

        unsafe {
            let ptr = { self.initializer_mut().all_uninit_vectors_mut().as_mut_ptr() };
            let filled = core::slice::from_raw_parts_mut(ptr, self.vectors_filled());
            crate::Init::cast_from_slices_mut(filled)
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
    /// Get the entire current vector as a mutable possibly-uninitialized slice, or None if all
    /// vectors are already filled.
    ///
    /// # Safety
    ///
    /// The caller must not allow the returned slice to be de-initialized in safe code.
    #[inline]
    pub unsafe fn current_vector_all_mut(&mut self) -> Option<&mut [MaybeUninit<u8>]> {
        self.debug_assert_validity();

        let all_vectors_mut = self.initializer.all_uninit_vectors_mut();

        if self.vectors_filled == all_vectors_mut.len() {
            None
        } else {
            Some(
                all_vectors_mut
                    .get_unchecked_mut(self.vectors_filled)
                    .as_maybe_uninit_slice_mut(),
            )
        }
    }
    #[inline]
    pub fn current_vector_init_uninit_parts(&self) -> Option<(&[u8], &[MaybeUninit<u8>])> {
        self.debug_assert_validity();

        let ordering = self
            .vectors_filled()
            .cmp(&self.initializer().vectors_initialized());

        match ordering {
            // The current vector is filled, but there are one or more vectors in front of it, that
            // are already initialized. We can thus simply assume that the current vector is
            // completely initialized.
            core::cmp::Ordering::Less => Some((
                unsafe { crate::cast_uninit_to_init_slice(self.current_vector_all()?) },
                &[],
            )),

            // The current vector (when tracking how they're filled) is behind one in front of it
            // that is not yet initialized. This cannot happen, and is library UB.
            core::cmp::Ordering::Greater => unsafe { core::hint::unreachable_unchecked() },

            // If the current vector is both in the initializing and in the filling phase, then we
            // will need to split it according to the initializer.
            core::cmp::Ordering::Equal => self.initializer().current_vector_init_uninit_parts(),
        }
    }
    #[inline]
    pub fn current_vector_init_uninit_parts_mut(
        &mut self,
    ) -> Option<(&mut [u8], &mut [MaybeUninit<u8>])> {
        self.debug_assert_validity();

        let ordering = self
            .vectors_filled()
            .cmp(&self.initializer().vectors_initialized());

        match ordering {
            // NOTE: See current_vector_init_uninit_parts. I'm lazy and I don't strive to avoid
            // redundancy, except at the API level :-)
            core::cmp::Ordering::Less => Some((
                unsafe { crate::cast_uninit_to_init_slice_mut(self.current_vector_all_mut()?) },
                &mut [],
            )),
            core::cmp::Ordering::Greater => unsafe { core::hint::unreachable_unchecked() },
            core::cmp::Ordering::Equal => self
                .initializer_mut()
                .current_vector_init_uninit_parts_mut(),
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
    pub fn current_vector_filled_part_mut(&mut self) -> Option<&mut [u8]> {
        self.debug_assert_validity();

        unsafe {
            let base_ptr = { self.current_vector_all_mut()?.as_mut_ptr() };
            Some(core::slice::from_raw_parts_mut(
                base_ptr as *mut u8,
                self.bytes_filled_for_vector,
            ))
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
    /// Retrieve all of the unfilled part as a single possibly-uninitialized mutable reference.
    // TODO: explain better
    /// # Safety
    ///
    /// Since the returned slice could contain both the unfilled but initialized, and the unfilled
    /// and uninitialized, this allows it to overlap. Thus, the caller must not de-initialize the
    /// resulting slice in any way, in safe code.
    #[inline]
    pub unsafe fn current_vector_unfilled_all_part_mut(
        &mut self,
    ) -> Option<&mut [MaybeUninit<u8>]> {
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

        let is_within =
            vectors_filled != total_vector_count && after_vectors_filled != total_vector_count;

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

        let is_within =
            vectors_filled != total_vector_count && after_vectors_filled != total_vector_count;

        if is_within {
            unsafe {
                let src_ptr = { self.initializer_mut().all_uninit_vectors_mut().as_mut_ptr() };
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
    /// the current vector in progress.
    pub fn all_filled_vectors(&self) -> (&[crate::Init<T::UninitVector>], &[u8]) {
        // TODO: Distinguish between None and Some(&[]). Do we really want optional values, when
        // empty slices work too?
        (
            self.all_previously_filled_vectors(),
            self.current_vector_filled_part().unwrap_or(&[]),
        )
    }
    /// For the current vector, return the unfilled and initialized part, the unfilled but
    /// initialized part, and the unfilled and uninitialized part, in that order.
    ///
    /// Note that unlike [`current_vector_all_mut`], the exclusive aliasing rules that come with
    /// mutable references are not needed here. The same result as calling this can be achieved by
    /// calling the finer-grained methods that access the individual parts of the current vector.
    ///
    /// [`current_vector_all_mut`]: #method.current_vector_all_mut
    // FIXME: which ones?
    pub fn current_vector_parts(&self) -> Option<VectorParts<'_>> {
        self.debug_assert_validity();

        unsafe {
            let (src_ptr, src_len) = {
                let src = self.current_vector_all()?;

                (src.as_ptr(), src.len())
            };

            let filled_base_ptr = src_ptr as *const u8;
            let filled_len = self.bytes_filled_for_vector;

            let init_len = self
                .initializer()
                .bytes_initialized_for_vector_unchecked(self.vectors_filled);

            let unfilled_init_base_ptr = src_ptr.add(self.bytes_filled_for_vector) as *const u8;
            let unfilled_init_len = init_len - filled_len;

            let unfilled_uninit_base_ptr = src_ptr.add(init_len);
            let unfilled_uninit_len = src_len - init_len;

            let filled = core::slice::from_raw_parts(filled_base_ptr, filled_len);
            let unfilled_init =
                core::slice::from_raw_parts(unfilled_init_base_ptr, unfilled_init_len);
            let unfilled_uninit =
                core::slice::from_raw_parts(unfilled_uninit_base_ptr, unfilled_uninit_len);

            Some(VectorParts {
                filled,
                unfilled_init,
                unfilled_uninit,
            })
        }
    }
    /// For the current vector, return the unfilled and initialized part, the unfilled but
    /// initialized part, and the unfilled and uninitialized part mutably, in that order.
    pub fn current_vector_parts_mut(&mut self) -> Option<VectorPartsMut<'_>> {
        self.debug_assert_validity();

        unsafe {
            let (src_ptr, src_len) = {
                let src = self.current_vector_all_mut()?;

                (src.as_mut_ptr(), src.len())
            };

            let filled_base_ptr = src_ptr as *mut u8;
            let filled_len = self.bytes_filled_for_vector;

            let init_len = self
                .initializer()
                .bytes_initialized_for_vector_unchecked(self.vectors_filled);

            let unfilled_init_base_ptr = src_ptr.add(self.bytes_filled_for_vector) as *mut u8;
            let unfilled_init_len = init_len - filled_len;

            let unfilled_uninit_base_ptr = src_ptr.add(init_len);
            let unfilled_uninit_len = src_len - init_len;

            let filled = core::slice::from_raw_parts_mut(filled_base_ptr, filled_len);
            let unfilled_init =
                core::slice::from_raw_parts_mut(unfilled_init_base_ptr, unfilled_init_len);
            let unfilled_uninit =
                core::slice::from_raw_parts_mut(unfilled_uninit_base_ptr, unfilled_uninit_len);

            Some(VectorPartsMut {
                filled,
                unfilled_init,
                unfilled_uninit,
            })
        }
    }
    fn debug_assert_validity(&self) {
        debug_assert!(self.bytes_filled_for_vector <= isize::MAX as usize);
        debug_assert!(self.vectors_filled <= self.initializer().total_vector_count());
        debug_assert!(self.vectors_filled <= self.initializer().vectors_initialized());
        // TODO
    }
    #[inline]
    pub fn total_vector_count(&self) -> usize {
        self.initializer().total_vector_count()
    }
    #[inline]
    pub fn vectors_remaining(&self) -> usize {
        self.total_vector_count()
            .wrapping_sub(self.vectors_filled())
    }
    pub fn count_remaining_bytes_to_fill(&self) -> usize {
        self.remaining_for_current_vector()
            + self
                .all_next_unfilled_vectors()
                .iter()
                .map(|unfilled_vector| unfilled_vector.as_maybe_uninit_slice().len())
                .sum::<usize>()
    }
    pub fn count_total_bytes_in_all_vectors(&self) -> usize {
        self.initializer().count_total_bytes_in_all_vectors()
    }
    /// Get the number of bytes that remain before the current vector becomes fully filled.
    ///
    /// If there is no current vector, which is the condition when all vectors have been filled,
    /// then this returns zero.
    #[inline]
    pub fn remaining_for_current_vector(&self) -> usize {
        self.current_vector_all().map_or(0, |current_vector| {
            current_vector.len() - self.bytes_filled_for_vector
        })
    }
    /// Advance the current vector by `count` bytes.
    ///
    /// # Panics
    ///
    /// This will panic if the initialized part of the current vector is exceeded. When calling
    /// this in FFI contexts, you must call the advance functions in the initializer before calling
    /// this.
    pub fn advance_current_vector(&mut self, count: usize) {
        let current_vector_all_len = match self.current_vector_all() {
            Some(current) => current.len(),
            None => panic!(
                "cannot advance the current vector by {} B, since no vectors were left",
                count
            ),
        };

        let ordering = Ord::cmp(
            &self.vectors_filled(),
            &self.initializer().vectors_initialized(),
        );

        let end = self.bytes_filled_for_vector + count;

        match ordering {
            core::cmp::Ordering::Equal => {
                assert!(
                    end <= self.initializer().bytes_initialized_for_current_vector(),
                    "cannot advance the fill count beyond the initialized part"
                );
                debug_assert!(end <= current_vector_all_len);
            }
            core::cmp::Ordering::Less => {
                assert!(
                    end <= current_vector_all_len,
                    "cannot advance the current vector beyond the end"
                );
            }
            core::cmp::Ordering::Greater => unsafe { core::hint::unreachable_unchecked() },
        }

        self.bytes_filled_for_vector += end;

        if self.bytes_filled_for_vector == current_vector_all_len {
            self.vectors_filled += 1;
            self.bytes_filled_for_vector = 0;
        }
    }
    pub fn advance_to_current_vector_end(&mut self) {
        let current_vector_all = match self.current_vector_all() {
            Some(current) => current,
            None => {
                panic!("cannot advance the current vector to end, when there are no vectors left")
            }
        };

        let ordering = Ord::cmp(
            &self.vectors_filled(),
            &self.initializer().vectors_initialized(),
        );

        match ordering {
            core::cmp::Ordering::Equal => assert_eq!(
                self.initializer().bytes_initialized_for_current_vector(),
                current_vector_all.len()
            ),
            core::cmp::Ordering::Less => (),
            core::cmp::Ordering::Greater => unsafe { core::hint::unreachable_unchecked() },
        }

        self.vectors_filled += 1;
        self.bytes_filled_for_vector = 0;
    }
    pub fn with_current_vector_unfilled_zeroed(&mut self) -> Option<&mut [u8]> {
        let _ = self.current_vector_all()?;

        let ordering = Ord::cmp(
            &self.vectors_filled(),
            &self.initializer().vectors_initialized(),
        );

        match ordering {
            // If the current vector is not fully initialized, we must first initialize the rest,
            // before returning the vector as initialized.
            core::cmp::Ordering::Equal => {
                self.initializer_mut().zero_current_vector_uninit_part();
            }
            // No need to initialize anything since the initialized vectors are already ahead of
            // the vectors that need to be filled.
            core::cmp::Ordering::Less => (),
            core::cmp::Ordering::Greater => unsafe { core::hint::unreachable_unchecked() },
        }

        Some(unsafe {
            let current_vector_all = self.current_vector_all_mut().expect(
                "expected the current vector to exist, since an earlier check has been done",
            );

            crate::cast_uninit_to_init_slice_mut(current_vector_all)
        })
    }
}
#[derive(Clone, Copy, Debug, Default)]
pub struct VectorParts<'a> {
    pub filled: &'a [u8],
    pub unfilled_init: &'a [u8],
    pub unfilled_uninit: &'a [MaybeUninit<u8>],
}
#[derive(Debug, Default)]
pub struct VectorPartsMut<'a> {
    pub filled: &'a mut [u8],
    pub unfilled_init: &'a mut [u8],
    pub unfilled_uninit: &'a mut [MaybeUninit<u8>],
}

pub struct BuffersRef<'buffers, T> {
    inner: &'buffers mut Buffers<T>,
}
impl<T> Buffers<T> {
    #[inline]
    pub fn by_ref(&mut self) -> BuffersRef<'_, T> {
        BuffersRef { inner: self }
    }
}
impl<'buffers, T> BuffersRef<'buffers, T> {
    #[inline]
    pub fn by_ref(&mut self) -> BuffersRef<'_, T> {
        BuffersRef { inner: self.inner }
    }
}
impl<'buffers, T> BuffersRef<'buffers, T>
where
    T: InitializeVectored,
{
    pub fn with_current_vector_unfilled_zeroed(&mut self) -> Option<&mut [u8]> {
        self.inner.with_current_vector_unfilled_zeroed()
    }
    pub fn advance_current_vector(&mut self, count: usize) {
        self.inner.advance_current_vector(count)
    }
    pub fn advance_to_current_vector_end(&mut self) {
        self.inner.advance_to_current_vector_end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn baisc_buffers_ops() {
        let mut a = [MaybeUninit::<u8>::uninit(); 32];
        let mut b = [MaybeUninit::uninit(); 8];
        let mut c = [MaybeUninit::uninit(); 16];
        let mut d = [MaybeUninit::uninit(); 9];

        let vectors = [&mut a[..], &mut b[..], &mut c[..], &mut d[..]];
        let buffers = Buffers::new(vectors);

        assert_eq!(buffers.vectors_filled(), 0);
        //assert_eq!(buffers.vectors_remaining(), 4);
    }
    #[test]
    fn with_current_vector_unfilled_zeroed() {
        let mut a = [MaybeUninit::<u8>::uninit(); 32];
        let mut b = [MaybeUninit::uninit(); 8];
        let mut c = [MaybeUninit::uninit(); 16];
        let mut d = [MaybeUninit::uninit(); 9];

        let mut vectors = [&mut a[..], &mut b[..], &mut c[..], &mut d[..]];
        let mut buffers = Buffers::new(&mut vectors[..]);
        let text = b"Hello, world!";

        while let Some(slice) = buffers.with_current_vector_unfilled_zeroed() {
            let to_copy = core::cmp::min(slice.len(), text.len());
            slice[..to_copy].copy_from_slice(&text[..to_copy]);
            buffers.advance_to_current_vector_end();
        }
        // TODO: Check that the vectors have the correct values.
    }
}
