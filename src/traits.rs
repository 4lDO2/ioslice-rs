use core::mem::MaybeUninit;

use crate::iovec::*;
use crate::iovec::init_marker::*;

#[cfg(feature = "alloc")]
use {
    alloc::boxed::Box,
    alloc::vec::Vec,
};

/// A trait for mutable initializable slices, that provide access to all the data required for
/// initialization, before the data can be assumed to be fully initialized.
///
/// # Safety
///
/// This trait is unsafe to implement since whatever slices are returned from the casts here,
/// __must have the same length and point to the same memory as before__. This is to allow safer
/// abstractions to assume that there are has not unexpectedly appeared additional bytes that must
/// be initialized.
///
/// In the future, when `&[u8]` starts implementing `AsRef<[MaybeUninit<u8>]>`, then this
/// implementation must also ensure that the `AsRef` implementation is correct.
pub unsafe trait Initialize: Sized {
    /// Retrieve an immutable slice pointing to possibly uninitialized memory. __This must be
    /// exactly the same slice as the one from [`as_maybe_uninit_slice_mut`], or the trait
    /// implementation as a whole, gets incorrect.__
    ///
    /// [`as_maybe_uninit_slice_mut`]: #tymethod.as_maybe_uninit_slice_mut
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>];

    /// Retrieve a mutable slice pointing to possibly uninitialized memory. __This must always
    /// point to the same slice as with previous invocations__, and it must be safe to call
    /// [`assume_init`] when all bytes here are overwritten.
    ///
    /// # Safety
    ///
    /// The caller must not use the resulting slice to de-initialize the data.
    ///
    /// [`assume_init`]: #tymethod.assume_init
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>];
}

/// A trait for slices (or owned memory) that contain possibly uninitialized slices themselves.
/// That is, the [`Initialize`] trait but for singly-indirect slices.
///
/// # Safety
///
/// For this trait to be implemented correctly, [`as_maybe_uninit_slice`] and
/// [`as_maybe_uninit_slice_mut`] must always return the same slices (albeit with different
/// aliasing rules as they take `&self` and `&mut self` respectively). Additionally, the
/// [`assume_init_all`] method must assume initializedness of exactly these slices.
///
/// [`assume_init_all`]: #tymethod.assume_init_all
/// [`as_maybe_uninit_slice`]: #tymethod.as_maybe_uninit_slice
/// [`as_maybe_uninit_slice_mut`]: #tymethod.as_maybe_uninit_slice_mut
// XXX: It would be __really__ useful to be able to unify the InitializeIndirectExt and
// InitializeExt traits, since they provide an identical interface, but with different
// requirements. This could perhaps be abstracted, but the best solution would be to use
// specialization, and maybe negative impls, to remove the possibility of conflict between the two
// traits.
pub unsafe trait InitializeVectored: Sized {
    /// The possibly uninitialized vector type, which must implement [`Initialize`], with
    /// [`Self::InitVector`] being the target. Note that this does not necessarily need to deref
    /// into [`MaybeUninit<u8>`], but can be anything that is convertible to it.
    type UninitVector: Initialize;

    /// Get the uninitialized version of all vectors. This slice must always be exactly equal to
    /// the slice returned by [`as_maybe_uninit_slice_mut`], or the trait is unsoundly implemented.
    ///
    /// [`as_maybe_uninit_slice_mut`]: #tymethod.as_maybe_uninit_slice_mut
    fn as_maybe_uninit_vectors(&self) -> &[Self::UninitVector];

    /// Get the uninitialized version of all vectors, mutably. This slice must always be exactly
    /// equal to the slice returned by [`as_maybe_uninit_slice`], or the trait is unsoundly
    /// implemented.
    ///
    /// # Safety
    ///
    /// For the user of this trait, the resulting slice returned from this method _must not_ be
    /// used to de-initialize the vectors by overwriting their contents with
    /// [`MaybeUninit::uninit`] if they were already initialized.
    ///
    /// [`as_maybe_uninit_slice`]: #tymethod.as_maybe_uninit_slice
    unsafe fn as_maybe_uninit_vectors_mut(&mut self) -> &mut [Self::UninitVector];
}
pub trait InitializeExt: private2::Sealed + Initialize {
    /// Assume that the type is already initialized. This is equivalent of calling [`Init::new`].
    ///
    /// # Safety
    ///
    /// The initialization invariant must be upheld for this to be safe.
    unsafe fn assume_init(self) -> crate::wrappers::Init<Self> {
        crate::wrappers::Init::new(self)
    }
    #[inline]
    fn init_by_filling(mut self, byte: u8) -> crate::wrappers::Init<Self> {
        unsafe {
            crate::fill_uninit_slice(self.as_maybe_uninit_slice_mut(), byte);
            self.assume_init()
        }
    }

    #[inline]
    fn init_by_copying(mut self, source: &[u8]) -> crate::wrappers::Init<Self> {
        unsafe {
            let slice = self.as_maybe_uninit_slice_mut();
            assert_eq!(source.len(), slice.len(), "in order to fully initialize a slice-like type, the source slice must be exactly as large");
            slice.copy_from_slice(crate::cast_init_to_uninit_slice(source));
            self.assume_init()
        }
    }
}
mod private2 {
    pub trait Sealed {}
}
mod private3 {
    pub trait Sealed {}
}
mod private4 {
    pub trait Sealed {}
}
mod private5 {
    pub trait Sealed {}
}

impl<T> private2::Sealed for T where T: Initialize {}
impl<T> InitializeExt for T where T: Initialize {}

unsafe impl<'a, I: InitMarker> Initialize for IoSliceMut<'a, I> {
    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        #[forbid(unconditional_recursion)]
        IoSliceMut::as_maybe_uninit_slice(self)
    }
    #[inline]
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        #[forbid(unconditional_recursion)]
        IoSliceMut::as_maybe_uninit_slice_mut(self)
    }
}
impl<'a, I: InitMarker> From<crate::wrappers::Init<IoSliceMut<'a, I>>> for IoSliceMut<'a, Init> {
    #[inline]
    fn from(init_ioslice: crate::wrappers::Init<IoSliceMut<'a, I>>) -> IoSliceMut<'a, Init> {
        #[forbid(unconditional_recursion)]
        unsafe {
            IoSliceMut::assume_init(init_ioslice.into_inner())
        }
    }
}
// TODO: splitting for IoSliceMut

unsafe impl<'a> Initialize for &'a mut [u8] {
    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        crate::cast_init_to_uninit_slice(self)
    }
    #[inline]
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        crate::cast_init_to_uninit_slice_mut(self)
    }
}
unsafe impl<'a> Initialize for &'a mut [MaybeUninit<u8>] {
    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        self
    }
    #[inline]
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self
    }
}
impl<'a, T> From<crate::wrappers::Init<&'a mut [MaybeUninit<T>]>> for &'a mut [T] {
    #[inline]
    fn from(init_slice: crate::wrappers::Init<&'a mut [MaybeUninit<T>]>) -> &'a mut [T] {
        unsafe { crate::cast_uninit_to_init_slice_mut(init_slice.into_inner()) }
    }
}
unsafe impl<T> InitializeVectored for T
where
    T: Initialize,
{
    type UninitVector = Self;

    #[inline]
    fn as_maybe_uninit_vectors(&self) -> &[Self::UninitVector] {
        core::slice::from_ref(self)
    }
    #[inline]
    unsafe fn as_maybe_uninit_vectors_mut(&mut self) -> &mut [Self::UninitVector] {
        core::slice::from_mut(self)
    }
}
unsafe impl<'a, 'b> InitializeVectored for &'a mut [&'b mut [MaybeUninit<u8>]] {
    type UninitVector = &'b mut [MaybeUninit<u8>];

    fn as_maybe_uninit_vectors(&self) -> &[Self::UninitVector] {
        self
    }
    unsafe fn as_maybe_uninit_vectors_mut(&mut self) -> &mut [Self::UninitVector] {
        self
    }
}
unsafe impl<'a, 'b, I: InitMarker> InitializeVectored for &'b mut [IoSliceMut<'a, I>] {
    type UninitVector = IoSliceMut<'a, Uninit>;

    #[inline]
    fn as_maybe_uninit_vectors(&self) -> &[Self::UninitVector] {
        IoSliceMut::cast_to_uninit_slices(self)
    }
    #[inline]
    unsafe fn as_maybe_uninit_vectors_mut(&mut self) -> &mut [Self::UninitVector] {
        IoSliceMut::cast_to_uninit_slices_mut(self)
    }
}
#[cfg(feature = "alloc")]
unsafe impl Initialize for Box<[u8]> {
    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        crate::cast_init_to_uninit_slice(self)
    }
    #[inline]
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        crate::cast_init_to_uninit_slice_mut(self)
    }
}
#[cfg(feature = "alloc")]
unsafe impl Initialize for Box<[MaybeUninit<u8>]> {
    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        self
    }
    #[inline]
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self
    }
}
#[cfg(feature = "alloc")]
impl From<crate::wrappers::Init<Box<[MaybeUninit<u8>]>>> for Box<[u8]> {
    #[inline]
    fn from(init_box: crate::wrappers::Init<Box<[MaybeUninit<u8>]>>) -> Box<[u8]> {
        #[cfg(feature = "nightly")]
        unsafe {
            #[forbid(unconditional_recursion)]
            Box::<[MaybeUninit<u8>]>::assume_init(init_box.into_inner())
        }
        #[cfg(not(feature = "nightly"))]
        unsafe {
            let slice_ptr = Box::into_raw(init_box.into_inner());
            Box::from_raw(crate::cast_uninit_to_init_slice_mut(&mut *slice_ptr))
        }
    }
}
#[cfg(feature = "alloc")]
unsafe impl Initialize for Vec<u8> {
    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        crate::cast_init_to_uninit_slice(&*self)
    }
    #[inline]
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        // TODO: Give the whole allocation, and not just the length set? With MaybeUninit, calling
        // set_len is safe.
        crate::cast_init_to_uninit_slice_mut(&mut *self)
    }
}
#[cfg(feature = "alloc")]
unsafe impl Initialize for Vec<MaybeUninit<u8>> {
    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        &*self
    }
    #[inline]
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        &mut *self
    }
}
#[cfg(feature = "alloc")]
impl From<crate::wrappers::Init<Vec<MaybeUninit<u8>>>> for Vec<u8> {
    #[inline]
    fn from(init_vec: crate::wrappers::Init<Vec<MaybeUninit<u8>>>) -> Vec<u8> {
        unsafe {
            let mut vec = init_vec.into_inner();
            //let (ptr, cap, len) = Vec::into_raw_parts(self);

            let (ptr, cap, len) = {
                let ptr = vec.as_mut_ptr();
                let cap = vec.capacity();
                let len = vec.len();

                core::mem::forget(vec);

                (ptr, cap, len)
            };

            Vec::from_raw_parts(ptr as *mut u8, cap, len)
        }
    }
}
