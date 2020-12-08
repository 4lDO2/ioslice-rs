use core::borrow::{Borrow, BorrowMut};
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};

use crate::iovec::*;
use crate::iovec::init_marker::*;
use crate::traits::Initialize;

/// A wrapper over `T` that assumes all of `T` to be initialized.
#[repr(transparent)]
#[derive(Clone, Copy, Default)]
pub struct Init<T> {
    inner: T,
}

impl<T> Init<T> {
    /// Wrap a possibly-uninitialized value `inner` into, assuming that it is fully initialized.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `inner` is fully initialized before this function can be
    /// called.
    #[inline]
    pub const unsafe fn new(inner: T) -> Self {
        Self { inner }
    }
    /// Cast `&[T]` to `&[Init<T>]`.
    ///
    /// # Safety
    ///
    /// This is unsafe because the caller has to ensure that all instances of type `T`, uphold the
    /// initialization invariant.
    #[inline]
    pub unsafe fn cast_from_slices(inner_slices: &[T]) -> &[Self] {
        // SAFETY: This is safe because Init is #[repr(transparent)], making the slices have the
        // same layout. The only contract that the caller has to follow, is that the data must
        // actually be initialized.
        core::slice::from_raw_parts(inner_slices.as_ptr() as *const Self, inner_slices.len())
    }
    /// Cast `&mut [T]` to `&mut [Init<T>]`.
    ///
    /// # Safety
    ///
    /// This is unsafe because the caller has to ensure that all instances of type `T`, uphold the
    /// initialization invariant.
    #[inline]
    pub unsafe fn cast_from_slices_mut(inner_slices: &mut [T]) -> &mut [Self] {
        // SAFETY: This is safe because Init is #[repr(transparent)], making the slices have the
        // same layout. The only contract that the caller has to follow, is that the data must
        // actually be initialized.
        core::slice::from_raw_parts_mut(inner_slices.as_ptr() as *mut Self, inner_slices.len())
    }
    /// Cast `&[Init<T>]` to `&mut [Init<T>]`.
    #[inline]
    pub fn cast_to_uninit_slices(selves: &[Self]) -> &[T] {
        unsafe {
            // SAFETY: This is safe because Init is #[repr(transparent)], making the slices have the
            // same layout.
            //
            // Since the returned slice is immutable, nothing can be deinitialized.
            core::slice::from_raw_parts(selves.as_ptr() as *const T, selves.len())
        }
    }
    /// Cast `&mut [Init<T>]` to `&mut [T]`.
    ///
    /// # Safety
    ///
    /// This is unsafe because it allows for de-initialization, which is very unlikely to happen by
    /// accident in practice, but which still would be unsound. The caller must simply never
    /// overwrite an already initialized value with [`MaybeUninit::uninit()`].
    #[inline]
    pub unsafe fn cast_to_uninit_slices_mut(selves: &mut [Self]) -> &mut [T] {
        // SAFETY: This is safe because Init is #[repr(transparent)], making the slices have the
        // same layout. The only contract that the caller has to follow, is that the data must
        // never be de-initialized.
        core::slice::from_raw_parts_mut(selves.as_ptr() as *mut T, selves.len())
    }
    #[inline]
    pub fn from_ref(inner_slice: &T) -> &Self {
        unsafe {
            // SAFETY: This is safe because Init is #[repr(transparent)], making the references
            // have the same layout. The only contract that the caller has to follow, is that the
            // data must actually be initialized.
            &*(inner_slice as *const T as *const Self)
        }
    }
    #[inline]
    pub fn from_mut(inner_slice: &mut T) -> &mut Self {
        unsafe {
            // SAFETY: This is safe because Init is #[repr(transparent)], making the references
            // have the same layout. The only contract that the caller has to follow, is that the
            // data must actually be initialized.
            &mut *(inner_slice as *mut T as *mut Self)
        }
    }
    #[inline]
    pub fn into_inner(self) -> T {
        self.inner
    }
    #[inline]
    pub const fn inner(&self) -> &T {
        &self.inner
    }
    #[inline]
    pub fn inner_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}
impl<T> Init<T>
where
    T: Initialize,
{
    #[inline]
    pub fn get_init_ref(&self) -> &[u8] {
        unsafe { crate::cast_uninit_to_init_slice(self.inner().as_maybe_uninit_slice()) }
    }
    #[inline]
    pub fn get_init_mut(&mut self) -> &mut [u8] {
        unsafe {
            crate::cast_uninit_to_init_slice_mut(self.inner_mut().as_maybe_uninit_slice_mut())
        }
    }
    #[inline]
    pub fn get_uninit_ref(&self) -> &[MaybeUninit<u8>] {
        self.inner().as_maybe_uninit_slice()
    }
    /// Get a mutable slice to the inner uninitialized slice.
    ///
    /// # Safety
    ///
    /// Since the [`Initialize`] trait is generic over both already initialized and uninitialized
    /// types, it is unsafe to retrieve an uninitialized slice to already initialized data, because
    /// it allows for de-initialization. (This can happen when overwriting the resulting slice with
    /// [`MaybeUninit::uninit()`].
    #[inline]
    pub unsafe fn get_uninit_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.inner_mut().as_maybe_uninit_slice_mut()
    }
}
impl<T> AsRef<[u8]> for Init<T>
where
    T: Initialize,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.get_init_ref()
    }
}
impl<T> AsMut<[u8]> for Init<T>
where
    T: Initialize,
{
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        self.get_init_mut()
    }
}
impl<T> AsRef<[MaybeUninit<u8>]> for Init<T>
where
    T: Initialize,
{
    #[inline]
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        self.get_uninit_ref()
    }
}
impl<T> Borrow<[u8]> for Init<T>
where
    T: Initialize,
{
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.get_init_ref()
    }
}
impl<T> BorrowMut<[u8]> for Init<T>
where
    T: Initialize,
{
    #[inline]
    fn borrow_mut(&mut self) -> &mut [u8] {
        self.get_init_mut()
    }
}
impl<T> Deref for Init<T>
where
    T: Initialize,
{
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        self.get_init_ref()
    }
}
impl<T> DerefMut for Init<T>
where
    T: Initialize,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut [u8] {
        self.get_init_mut()
    }
}
impl<T> PartialEq for Init<T>
where
    T: Initialize,
{
    fn eq(&self, other: &Self) -> bool {
        self.get_init_ref() == other.get_init_ref()
    }
}
impl<T> Eq for Init<T> where T: Initialize {}
impl<T> PartialOrd for Init<T>
where
    T: Initialize,
{
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}
impl<T> Ord for Init<T>
where
    T: Initialize,
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        Ord::cmp(self.get_init_ref(), other.get_init_ref())
    }
}
impl<T> core::hash::Hash for Init<T>
where
    T: Initialize,
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.get_init_ref().hash(state)
    }
}

#[repr(transparent)]
pub struct InitVectors<I> {
    inner: I,
}
impl<I> InitVectors<I> {
    pub const unsafe fn new_unchecked(inner: I) -> Self {
        Self {
            inner,
        }
    }
    #[inline]
    pub fn into_inner(self) -> I {
        self.inner
    }
}

impl<'a, 'b, I: InitMarker> From<InitVectors<&'b mut [IoSliceMut<'a, I>]>>
    for &'b mut [IoSliceMut<'a, init_marker::Init>]
{
    fn from(init_vectors: InitVectors<&'b mut [IoSliceMut<'a, I>]>) -> Self {
        unsafe { IoSliceMut::cast_to_init_slices_mut(init_vectors.into_inner()) }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Single<T>(pub T);

impl<T> AsRef<[T]> for Single<T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        core::slice::from_ref(&self.0)
    }
}
impl<T> AsMut<[T]> for Single<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        core::slice::from_mut(&mut self.0)
    }
}
impl<T> AsRef<T> for Single<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.0
    }
}
impl<T> AsMut<T> for Single<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}
impl<T> Borrow<T> for Single<T> {
    #[inline]
    fn borrow(&self) -> &T {
        &self.0
    }
}
impl<T> BorrowMut<T> for Single<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut T {
        &mut self.0
    }
}
impl<T> Borrow<[T]> for Single<T> {
    #[inline]
    fn borrow(&self) -> &[T] {
        core::slice::from_ref(&self.0)
    }
}
impl<T> BorrowMut<[T]> for Single<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        core::slice::from_mut(&mut self.0)
    }
}

impl<T> Deref for Single<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<T> DerefMut for Single<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
