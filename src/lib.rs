//! `#![no_std]`-friendly wrappers over the [`std::io::IoSlice`] and [`std::io::IoSliceMut`], which
//! are shared slices and exclusive slices, respectively, and ABI-compatible with system types for
//! I/O vectors.
//!
//! Internally, the struct will store the following based on crate features:
//!
//! * `std` - wrapping [`std::io::IoSlice`] directly, with accessors for it as well as conversion
//!   functions and From impls.
//! * `libc` (and `#[cfg(unix)]`) - wrapping [`libc::iovec`] directly on platforms that support it.
//!   A marker is also stored, to safely wrap the raw pointer, and forcing usage of this API to
//!   follow the borrow checker rules.
//! * (none) - wrapping a regular slice, that may not have the same ABI guarantees as the types
//!   from std or libc have.
//!
//! `IoSlice` will however implement `AsRef<[u8]>`, `Borrow<[u8]>`, and `Deref<Target = [u8]>`
//! regardless of the features used.

#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(feature = "nightly", feature(min_const_generics, slice_fill))]

#[cfg(all(unix, windows))]
compile_error!("cannot compile for both windows and unix");

mod private {
    pub trait Sealed {}
}

pub unsafe trait Initialization: private::Sealed {
    const IS_INITIALIZED: bool;
    type DerefTargetItem: fmt::Debug;
}

pub enum Initialized {}
pub enum Uninitialized {}

impl private::Sealed for Initialized {}
impl private::Sealed for Uninitialized {}

unsafe impl Initialization for Initialized {
    const IS_INITIALIZED: bool = true;
    type DerefTargetItem = u8;
}
unsafe impl Initialization for Uninitialized {
    const IS_INITIALIZED: bool = false;
    type DerefTargetItem = MaybeUninit<u8>;
}

use core::borrow::{Borrow, BorrowMut};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::{cmp, fmt, hash, ops};

#[allow(unused_imports)]
use core::mem;

#[cfg(all(windows, feature = "winapi"))]
use winapi::shared::{
    ntdef::{CHAR, ULONG},
    ws2def::WSABUF,
};

#[cfg(feature = "alloc")]
extern crate alloc;

/// A `#![no_std]`-friendly wrapper over the [`std::io::IoSliceMut`].
///
/// Internally, the struct will store the following based on crate features:
///
/// * `std` - wrapping [`std::io::IoSlice`] directly, with accessors for it as well as conversion
///   functions and From impls.
/// * `libc` (with `#[cfg(unix)]` - wrapping [`libc::iovec`] directly on platforms that support it.
/// * `winapi` (with `#[cfg(windows)]`) - wrapping `WSABUF` directly.
/// * (none) - wrapping a regular slice, that may not have the same ABI guarantees as the types
///   from std or libc have.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct IoSlice<'a, I: Initialization = Initialized> {
    #[cfg(all(unix, feature = "libc"))]
    inner: (libc::iovec, PhantomData<&'a [I::DerefTargetItem]>),

    #[cfg(all(windows, feature = "winapi"))]
    inner: (WSABUF, PhantomData<&'a [I::DerefTargetItem]>),

    #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
    inner: &'a [I::DerefTargetItem],

    _marker: PhantomData<I>,
}

// SAFETY: This is safe because whatever pointer that is sent to this slice must be Send in the
// first place. Regular slices implement Send and Sync because of this.
unsafe impl<'a, I: Initialization> Send for IoSlice<'a, I> {}
// SAFETY: Same as above.
unsafe impl<'a, I: Initialization> Sync for IoSlice<'a, I> {}
impl<'a, I: Initialization> Unpin for IoSlice<'a, I> {}

#[cfg(feature = "std")]
impl<'a, I: Initialization> std::panic::UnwindSafe for IoSlice<'a, I> {}
#[cfg(feature = "std")]
impl<'a, I: Initialization> std::panic::RefUnwindSafe for IoSlice<'a, I> {}

impl<'a, I: Initialization> IoSlice<'a, I> {
    /// Convert a regular slice into an I/O slice.
    ///
    /// The initializedness of the resulting I/O slice is dependent on the `I` generic parameter,
    /// which by default is [`Initialized`]. Note that it is highly recommended not to call this
    /// with [`Uninitialized`], since immutable slices cannot be made initialized, and one
    /// therefore has to prove externally that the memory is in fact initialized before using it.
    #[inline]
    pub fn new(slice: &'a [u8]) -> Self {
        unsafe { Self::__construct(slice.as_ptr(), slice.len()) }
    }

    /// Cast any I/O slice into an [`Uninitialized`] slice, forgetting about the original
    /// initializedness.
    #[inline]
    pub fn as_uninit(&self) -> &IoSlice<'a, Uninitialized> {
        unsafe { &*(self as *const Self as *const IoSlice<'a, Uninitialized>) }
    }
    #[inline]
    pub fn as_uninit_mut(&mut self) -> &mut IoSlice<'a, Uninitialized> {
        unsafe { &mut *(self as *mut Self as *mut IoSlice<'a, Uninitialized>) }
    }
    /// Turn any I/O slice into an [`Uninitialized`] slice, forgetting about the original
    /// initializedness.
    #[inline]
    pub fn into_uninit(self) -> IoSlice<'a, Uninitialized> {
        unsafe { IoSlice::__construct(self.__ptr(), self.__len()) }
    }

    /// Unsafely turn an I/O slice, being already [`Initialized`] or not, into an I/O slice that is [`Initialized`].
    ///
    /// # Safety
    ///
    /// For this to be safe, the initialization invariant must be upheld. Refer to the
    /// [`std::mem::MaybeUninit`] docs.
    #[inline]
    pub unsafe fn assume_init(self) -> IoSlice<'a, Initialized> {
        IoSlice::__construct(self.__ptr(), self.__len())
    }

    /// Wrap a system [`libc::iovec`] into a wrapped I/O slice, assuming the iovec can be
    /// represented as borrowed for the lifetime `'a`. If the iovec is otherwise owned and
    /// allocated via the system allocator, consider wrapping it in [`IoBox`] if the `alloc`
    /// feature is used.
    ///
    /// _This is only available on Unix targets with the `libc` feature enabled_.
    ///
    /// # Safety
    ///
    /// This is unsafe because the slice must be valid (refer to libstd's section about pointer and
    /// slice validity near [`std::ptr`]).
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub unsafe fn from_raw_iovec(slice: libc::iovec) -> Self {
        Self {
            inner: (slice, PhantomData),
            _marker: PhantomData,
        }
    }
    /// Retrieve the inner iovec from this I/O slice.
    ///
    /// The raw iovec must be considered borrowed from this slice, even though it is not tracked
    /// with a lifetime.
    ///
    /// _This is only available on Unix targets with the `libc` feature enabled_.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub fn as_raw_iovec(&self) -> libc::iovec {
        self.inner.0
    }

    /// Cast a slice of I/O slices into a slice of iovecs. Since these must share the same ABI
    /// layout, this is completely safe, and can be directly passed to system calls.
    ///
    /// _This is only available on Unix targets with the `libc` feature enabled_.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub fn cast_to_raw_iovecs(slices: &'a [Self]) -> &'a [libc::iovec] {
        unsafe { cast_slice_same_layout(slices) }
    }
    /// Cast a mutable slice of I/O slices into a mutable slice of iovecs. iovecs share the exact
    /// same ABI guarantees as this wrapper.
    ///
    /// _This is only available on Unix targets with the `libc` feature enabled_.
    ///
    /// # Safety
    ///
    /// This is unsafe, since the iovecs can be mutated, which will cause the original wrapped
    /// slices to be changed as well. If the iovecs are changed to invalid values in any way, this
    /// breaks the validity invariant upheld by this wrapped type, leading to UB.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub unsafe fn cast_to_raw_iovecs_mut(slices: &'a mut [Self]) -> &'a mut [libc::iovec] {
        cast_slice_same_layout_mut(slices)
    }

    /// Advance the start offset of an I/O slice, effectively shrinking it from the start.
    ///
    /// # Panics
    ///
    /// This will panic if count is greater than the current length. On Windows, this will also
    /// therefore instantly fail if count is greater than 2^32, since larger buffers cannot be
    /// constructed.
    #[inline]
    pub fn advance(&mut self, count: usize) {
        unsafe {
            self.__set_len(
                self.__len()
                    .checked_sub(count)
                    .expect("IoSlice::advance causes length to overflow"),
            );
            self.__set_ptr(self.__ptr().add(count));
        }
    }
    /// Advance a range of slices by a specific offset, by advancing each slice individually until
    /// the offset is reached.
    ///
    /// __Note that while this may modify the original slices in-place, the return value should
    /// always be used, since the original value may contain old slices that were completely
    /// skipped and never made empty__.
    ///
    /// This returns an Option rather than panicking when `n` is greater than the total length, to
    /// reduce the need for counting, or blind reliance on system call correctness.
    #[must_use]
    pub fn advance_within(mut slices: &mut [Self], mut n: usize) -> Option<&mut [Self]> {
        while let Some(buffer) = slices.first_mut() {
            if n == 0 {
                return Some(slices);
            };

            let buffer_len = buffer.len();

            if buffer_len > n {
                buffer.advance(n);
            } else {
                slices = &mut slices[1..];
            }
            n -= core::cmp::min(buffer_len, n);
        }
        if n > 0 {
            return None;
        }
        Some(slices)
    }
    /// Get a slice to the "inner data" pointed to by this slice, which may be either `[u8]` or
    /// `[MaybeUninit<u8>]`, depending on the `I` generic parameter. Prefer [`as_slice`] or
    /// [`as_maybe_uninit_slice`] instead; this is only used to make various methods easier to
    /// implement generically.
    ///
    /// [`as_slice`]: #method.as_slice
    /// [`as_maybe_uninit_slice`]: #method.as_maybe_uninit_slice
    #[inline]
    pub fn inner_data(&self) -> &'a [I::DerefTargetItem] {
        #[cfg(all(unix, feature = "libc"))]
        return unsafe {
            core::slice::from_raw_parts(self.inner.0.iov_base as *const _, self.inner.0.iov_len)
        };
        #[cfg(all(windows, feature = "winapi"))]
        return unsafe {
            core::slice::from_raw_parts(self.inner.0.buf as *const _, self.inner.0.len as usize)
        };

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        return unsafe {
            core::slice::from_raw_parts(self.inner.as_ptr() as *const _, self.inner.len())
        };
    }
    /// Construct an I/O slice based on the inner data, which is either `[u8]` or `[MaybeUninit]`.
    #[inline]
    pub fn from_inner_data(inner_data: &'a [I::DerefTargetItem]) -> Self {
        Self {
            #[cfg(all(unix, feature = "libc"))]
            inner: (
                libc::iovec {
                    iov_base: inner_data.as_ptr() as *mut libc::c_void,
                    iov_len: inner_data.len(),
                },
                PhantomData,
            ),

            #[cfg(all(windows, feature = "winapi"))]
            inner: (
                WSABUF {
                    len: inner_data.len() as ULONG,
                    buf: inner_data.as_ptr() as *mut CHAR,
                },
                PhantomData,
            ),

            #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
            inner: inner_data,

            _marker: PhantomData,
        }
    }
    /// Retrieve a slice of possibly uninitialized data, but which is still always valid.
    #[inline]
    pub fn as_maybe_uninit_slice(&self) -> &'a [MaybeUninit<u8>] {
        self.as_uninit().inner_data()
    }
    fn __ptr(&self) -> *const u8 {
        #[cfg(all(unix, feature = "libc"))]
        return self.inner.0.iov_base as *const u8;

        #[cfg(all(windows, feature = "winapi"))]
        return self.inner.0.buf as *const u8;

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        return self.inner.as_ptr() as *const u8;
    }
    fn __len(&self) -> usize {
        #[cfg(all(unix, feature = "libc"))]
        return self.inner.0.iov_len as usize;

        #[cfg(all(windows, feature = "winapi"))]
        return self.inner.0.len as usize;

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        return self.inner.len();
    }
    #[inline]
    unsafe fn __set_ptr(&mut self, ptr: *const u8) {
        #[cfg(all(unix, feature = "libc"))]
        {
            self.inner.0.iov_base = ptr as *mut libc::c_void;
        }

        #[cfg(all(windows, feature = "winapi"))]
        {
            self.inner.0.buf = ptr as *mut CHAR;
        }

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        {
            self.inner =
                core::slice::from_raw_parts(ptr as *const I::DerefTargetItem, self.__len());
        }
    }
    #[inline]
    unsafe fn __set_len(&mut self, len: usize) {
        #[cfg(all(unix, feature = "libc"))]
        {
            self.inner.0.iov_len = len as usize;
        }

        #[cfg(all(windows, feature = "libc"))]
        {
            use core::convert::TryInto;

            self.inner.0.len = len
                .try_into()
                .expect("length exceeding 2^32 bytes, which is the limit of WSABUF");
        }

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        {
            self.inner =
                core::slice::from_raw_parts(self.__ptr() as *const I::DerefTargetItem, len);
        }
    }
    unsafe fn __construct(ptr: *const u8, len: usize) -> Self {
        #[cfg(all(windows, feature = "winapi"))]
        use core::convert::TryInto;

        Self {
            #[cfg(all(unix, feature = "libc"))]
            inner: (
                libc::iovec {
                    iov_base: ptr as *mut libc::c_void,
                    iov_len: len as usize,
                },
                PhantomData,
            ),
            #[cfg(all(windows, feature = "winapi"))]
            inner: (
                WSABUF {
                    len: len.try_into().expect(
                        "Constructing an IoSlice that is larger than the 2^32 limit of WSABUF",
                    ),
                    buf: ptr as *mut CHAR,
                },
                PhantomData,
            ),
            #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
            inner: { core::slice::from_raw_parts(ptr as *const I::DerefTargetItem, len) },

            _marker: PhantomData,
        }
    }
}
impl<'a> IoSlice<'a, Initialized> {
    /// Retrieve an initialized byte slice from this I/O slice.
    #[inline]
    pub fn as_slice(&self) -> &'a [u8] {
        self.inner_data()
    }
    /// Convert this slice into an initialized [`std::io::IoSlice`].
    ///
    /// _This is only available with the `std` feature enabled_.
    #[cfg(feature = "std")]
    #[inline]
    pub fn into_std_ioslice(self) -> std::io::IoSlice<'a> {
        std::io::IoSlice::new(self.as_slice())
    }
    /// Cast a slice of I/O slices, into a slice of libstd's [`std::io::IoSlice`]. This is safe
    /// since they both must share the same ABI layout as [`libc::iovec`].
    ///
    /// _This is only available with the `std` feature enabled_.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_ioslices<'b>(slices: &'b [Self]) -> &'b [std::io::IoSlice<'a>] {
        unsafe { cast_slice_same_layout(slices) }
    }
    /// Cast a mutable slice of I/O slices, into a mutable slice of libstd's [`std::io::IoSlice`].
    /// This is safe since they both must share the same ABI layout as [`libc::iovec`], and since
    /// libstd's I/O slices have the same validity invariant as this wrapper and slices in general.
    ///
    /// _This is only available with the `std` feature enabled_.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_ioslices_mut(slices: &'a mut [Self]) -> &'a mut [std::io::IoSlice<'a>] {
        unsafe { cast_slice_same_layout_mut(slices) }
    }
}
impl<'a, I: Initialization> fmt::Debug for IoSlice<'a, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if I::IS_INITIALIZED {
            write!(f, "{:?}", self.inner_data())
        } else {
            write!(
                f,
                "[possibly uninitialized immutable I/O slice at {:p}, len {} bytes]",
                self.as_maybe_uninit_slice().as_ptr(),
                self.as_maybe_uninit_slice().len()
            )
        }
    }
}
impl<'a, I: Initialization> AsRef<[I::DerefTargetItem]> for IoSlice<'a, I> {
    #[inline]
    fn as_ref(&self) -> &[I::DerefTargetItem] {
        self.inner_data()
    }
}
impl<'a, I: Initialization> Borrow<[I::DerefTargetItem]> for IoSlice<'a, I> {
    #[inline]
    fn borrow(&self) -> &[I::DerefTargetItem] {
        self.inner_data()
    }
}
impl<'a, I: Initialization> ops::Deref for IoSlice<'a, I> {
    type Target = [I::DerefTargetItem];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner_data()
    }
}
impl<'a, I: Initialization> From<&'a [I::DerefTargetItem]> for IoSlice<'a, I> {
    #[inline]
    fn from(slice: &'a [I::DerefTargetItem]) -> Self {
        Self::from_inner_data(slice)
    }
}
impl<'a, I: Initialization> From<&'a mut [I::DerefTargetItem]> for IoSlice<'a, I> {
    #[inline]
    fn from(slice: &'a mut [I::DerefTargetItem]) -> Self {
        Self::from_inner_data(&*slice)
    }
}
impl<'a> From<&'a [u8]> for IoSlice<'a, Uninitialized> {
    fn from(maybe_uninit_slice: &'a [u8]) -> Self {
        Self::new(maybe_uninit_slice)
    }
}
impl<'a> From<&'a mut [u8]> for IoSlice<'a, Uninitialized> {
    fn from(maybe_uninit_slice: &'a mut [u8]) -> Self {
        Self::new(&*maybe_uninit_slice)
    }
}

#[cfg(feature = "nightly")]
impl<'a, I: Initialization, const N: usize> From<&'a [I::DerefTargetItem; N]> for IoSlice<'a, I> {
    #[inline]
    fn from(array_ref: &'a [I::DerefTargetItem; N]) -> Self {
        Self::from_inner_data(&array_ref[..])
    }
}
#[cfg(feature = "nightly")]
impl<'a, I: Initialization, const N: usize> From<&'a mut [I::DerefTargetItem; N]>
    for IoSlice<'a, I>
{
    #[inline]
    fn from(array_ref: &'a mut [I::DerefTargetItem; N]) -> Self {
        Self::from_inner_data(&array_ref[..])
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> From<&'a [u8; N]> for IoSlice<'a, Uninitialized> {
    #[inline]
    fn from(array_ref: &'a [u8; N]) -> Self {
        Self::new(&array_ref[..])
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> From<&'a mut [u8; N]> for IoSlice<'a, Uninitialized> {
    #[inline]
    fn from(array_ref: &'a mut [u8; N]) -> Self {
        Self::new(&array_ref[..])
    }
}
impl<'a> PartialEq for IoSlice<'a, Initialized> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self == other.as_slice()
    }
}
impl<'a> PartialEq<[u8]> for IoSlice<'a, Initialized> {
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialEq<[u8; N]> for IoSlice<'a, Initialized> {
    #[inline]
    fn eq(&self, other: &[u8; N]) -> bool {
        self == &other[..]
    }
}
impl<'a, 'b> PartialEq<IoSliceMut<'b, Initialized>> for IoSlice<'a, Initialized> {
    #[inline]
    fn eq(&self, other: &IoSliceMut<'b>) -> bool {
        self == other.as_slice()
    }
}

impl<'a> Eq for IoSlice<'a, Initialized> {}

impl<'a> PartialOrd<[u8]> for IoSlice<'a, Initialized> {
    #[inline]
    fn partial_cmp(&self, other: &[u8]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}
impl<'a, 'b> PartialOrd<IoSliceMut<'b, Initialized>> for IoSlice<'a, Initialized> {
    #[inline]
    fn partial_cmp(&self, other: &IoSliceMut<'b>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other.as_slice())
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialOrd<[u8; N]> for IoSlice<'a, Initialized> {
    #[inline]
    fn partial_cmp(&self, other: &[u8; N]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}

impl<'a> PartialOrd for IoSlice<'a, Initialized> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}
impl<'a> Ord for IoSlice<'a, Initialized> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(self.as_slice(), other.as_slice())
    }
}
impl<'a, I: Initialization> Default for IoSlice<'a, I> {
    #[inline]
    fn default() -> Self {
        Self::new(&[])
    }
}
impl<'a> hash::Hash for IoSlice<'a, Initialized> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        state.write(self.as_slice())
    }
}

#[cfg(feature = "std")]
impl<'a, I: Initialization> From<std::io::IoSlice<'a>> for IoSlice<'a, I> {
    #[inline]
    fn from(slice: std::io::IoSlice<'a>) -> Self {
        Self {
            // NOTE: `std::io::IoSlice` somehow has no method available to access the slice at
            // lifetime `'a`, but only the lifetime of the wrapped slice. Hence, we must do this
            // manually.
            // TODO: Is this possible?
            #[cfg(all(unix, feature = "libc"))]
            inner: (
                libc::iovec {
                    iov_base: slice.as_ptr() as *mut libc::c_void,
                    iov_len: slice.len(),
                },
                PhantomData,
            ),

            #[cfg(all(windows, feature = "winapi"))]
            inner: (
                WSABUF {
                    len: slice.len() as ULONG,
                    buf: slice.as_ptr() as *mut CHAR,
                },
                PhantomData,
            ),
            #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
            inner: unsafe {
                core::slice::from_raw_parts(
                    slice.as_ptr() as *const I::DerefTargetItem,
                    slice.len(),
                )
            },

            _marker: PhantomData,
        }
    }
}
#[cfg(feature = "std")]
impl<'a, I: Initialization> From<std::io::IoSliceMut<'a>> for IoSlice<'a, I> {
    #[inline]
    fn from(mut slice: std::io::IoSliceMut<'a>) -> Self {
        unsafe { Self::__construct(slice.as_mut_ptr(), slice.len()) }
    }
}
#[cfg(all(unix, feature = "libc"))]
impl<'a, I: Initialization> From<IoSlice<'a, I>> for libc::iovec {
    #[inline]
    fn from(slice: IoSlice<'a, I>) -> Self {
        slice.as_raw_iovec()
    }
}
#[cfg(feature = "stable_deref_trait")]
unsafe impl<'a, I: Initialization> stable_deref_trait::StableDeref for IoSlice<'a, I> {}

/// A `#![no_std]`-friendly wrapper over the [`std::io::IoSliceMut`].
///
/// Internally, the struct will store the following based on crate features:
///
/// * `std` - wrapping [`std::io::IoSliceMut`] directly, with accessors for it as well as conversion
///   functions and From impls.
/// * `libc` (with `#[cfg(unix)]` - wrapping [`libc::iovec`] directly on platforms that support it,
///   together with a marker making rustc think this stores a `&'a mut [u8]`.
/// * (none) - wrapping a regular slice, that may not have the same ABI guarantees as the types
///   from std or libc have.
#[repr(transparent)]
pub struct IoSliceMut<'a, I: Initialization = Initialized> {
    #[cfg(all(unix, feature = "libc"))]
    inner: (libc::iovec, PhantomData<&'a mut [I::DerefTargetItem]>),

    #[cfg(all(windows, feature = "winapi"))]
    inner: (WSABUF, PhantomData<&'a mut [I::DerefTargetItem]>),

    #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
    inner: &'a mut [I::DerefTargetItem],

    _marker: PhantomData<I>,
}
// SAFETY: Same as the safety section of impl Send for IoSlice.
unsafe impl<'a, I: Initialization> Send for IoSliceMut<'a, I> {}
// SAFETY: Same as the safety section of impl Send for IoSlice.
unsafe impl<'a, I: Initialization> Sync for IoSliceMut<'a, I> {}
impl<'a, I: Initialization> Unpin for IoSliceMut<'a, I> {}

#[cfg(feature = "std")]
impl<'a, I: Initialization> std::panic::UnwindSafe for IoSliceMut<'a, I> {}
#[cfg(feature = "std")]
impl<'a, I: Initialization> std::panic::RefUnwindSafe for IoSliceMut<'a, I> {}

impl<'a, I: Initialization> IoSliceMut<'a, I> {
    /// Construct a new mutable I/O slice, from an existing initialized slice. The initializedness
    /// is determined based on the generic parameter `I`, while the original slice obviously has to
    /// be initialized since its type is [`u8`] and not [`MaybeUninit<u8>`].
    #[inline]
    pub fn new(slice: &'a mut [u8]) -> Self {
        unsafe { Self::__construct(slice.as_mut_ptr(), slice.len()) }
    }
    /// Unsafely cast a possibly uninitialized slice into an initialized slice.
    ///
    /// __NOTE: THIS MUST NOT BE USED FOR INITIALIZATION; THAT IS DIRECT UB__
    ///
    /// # Safety
    ///
    /// For this to be safe, the initialization invariant must be upheld. Refer to the
    /// [`std::mem::MaybeUninit`] docs.
    #[inline]
    pub unsafe fn assume_init(self) -> IoSliceMut<'a, Initialized> {
        IoSliceMut::__construct(self.__ptr(), self.__len())
    }

    /// Unsafely cast a possibly uninitialized slice into an initialized slice, by reference.
    ///
    /// # Safety
    ///
    /// This must uphold the initialization invariant.
    #[inline]
    pub unsafe fn assume_init_ref(&self) -> &IoSliceMut<'a, Initialized> {
        &*(self as *const Self as *const IoSliceMut<'a, Initialized>)
    }
    /// Unsafely cast a possibly uninitialized slice into an initialized slice, by mutable reference.
    ///
    /// # Safety
    ///
    /// This must uphold the initialization invariant.
    #[inline]
    pub unsafe fn assume_init_mut(&mut self) -> &mut IoSliceMut<'a, Initialized> {
        &mut *(self as *mut Self as *mut IoSliceMut<'a, Initialized>)
    }

    /// Cast an I/O slice, being [`Initialized`] or not, into an [`Uninitialized`] I/O slice.
    #[inline]
    pub fn into_uninit(self) -> IoSliceMut<'a, Uninitialized> {
        unsafe { IoSliceMut::__construct(self.__ptr(), self.__len()) }
    }
    /// Cast an I/O slice, being [`Initialized`] or not, into an [`Uninitialized`] I/O slice, by
    /// reference.
    pub fn as_uninit(&self) -> &IoSliceMut<'a, Uninitialized> {
        unsafe { &*(self as *const Self as *const IoSliceMut<'a, Uninitialized>) }
    }
    /// Cast an I/O slice, being [`Initialized`] or not, into an [`Uninitialized`] I/O slice, by
    /// mutable reference.
    pub fn as_uninit_mut(&mut self) -> &mut IoSliceMut<'a, Uninitialized> {
        unsafe { &mut *(self as *mut Self as *mut IoSliceMut<'a, Uninitialized>) }
    }

    /// Wrap a system [`libc::iovec`] into this wrapper.
    ///
    /// _This is only available on Unix targets with the `libc` feature enabled_.
    ///
    /// # Safety
    ///
    /// For this to be safe, the validity invariant must be upheld, which takes things like size,
    /// alignment, concurrent use, etc. in parallel. In short, the slice must be considered mutably
    /// borrowed, and it must be safe to assume that it will not outlive the lifetime `'a`. Refer
    /// to the [`std::ptr`] docs for more information regarding validity.
    ///
    /// Additionally, if the `I` generic parameter is [`Initialized`], the iovec must also point to
    /// initialized data.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub unsafe fn from_raw_iovec(slice: libc::iovec) -> Self {
        Self {
            inner: (slice, PhantomData),
            _marker: PhantomData,
        }
    }
    /// Retrieve the wrapped raw [`libc::iovec ] from this wrapper.
    ///
    /// The resulting slice is considered immutable, even though it is neither UB nor more unsafe
    /// than [`as_raw_iovecs_mut`]. This simply exists to prevent accidentally obtaining a
    /// "mutable" [`libc::iovec`] where that is not possible (e.g. inside an [`std::sync::Arc`]).
    ///
    /// [`as_raw_iovecs_mut`]: #method.as_raw_iovecs_mut
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub fn as_raw_iovec(&self) -> libc::iovec {
        self.inner.0
    }
    /// Retrieve the wrapped raw [`libc::iovec ] from this wrapper, requiring exclusive access of
    /// this slice, to obtain.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub fn as_raw_iovec_mut(&mut self) -> libc::iovec {
        self.inner.0
    }
    /// Cast a slice of wrapped I/O slices into a slice of [`libc::iovec`]s.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub fn cast_to_raw_iovecs(slices: &[Self]) -> &[libc::iovec] {
        unsafe { cast_slice_same_layout(slices) }
    }
    /// Unsafely cast a mutable slice of wrapped I/O slices into a mutable slice of
    /// [`libc::iovec`]s.
    ///
    /// # Safety
    ///
    /// This is unsafe because the initialization or validity invariants may be broken since the
    /// iovecs can be changed arbitrarily in a mutable reference.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub unsafe fn cast_to_raw_iovecs_mut(slices: &mut [Self]) -> &mut [libc::iovec] {
        cast_slice_same_layout_mut(slices)
    }

    /// Unsafely cast a slice of [`libc::iovec`]s into a slice of [`IoSliceMut`].
    ///
    /// # Safety
    ///
    /// This is unsafe since the iovecs must uphold the validity and initialization invariants.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub unsafe fn from_raw_iovecs(slice: &[libc::iovec]) -> &[Self] {
        cast_slice_same_layout(slice)
    }
    /// Unsafely cast a mutable slice of [`libc::iovec`]s into a mutable slice of [`IoSliceMut`].
    ///
    /// # Safety
    ///
    /// This is unsafe since the iovecs must uphold the validity and initialization invariants.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub unsafe fn from_raw_iovecs_mut(slice: &mut [libc::iovec]) -> &mut [Self] {
        cast_slice_same_layout_mut(slice)
    }
    /// Advance the start offset of a single slice by `count` bytes, reducing the length as well.
    ///
    /// # Panics
    ///
    /// This will panic if `count` is greater than the current length.
    #[inline]
    pub fn advance(&mut self, count: usize) {
        unsafe {
            self.__set_len(
                self.__len()
                    .checked_sub(count)
                    .expect("IoSlice::advance causes length to overflow"),
            );
            self.__set_ptr(self.__ptr().add(count));
        }
    }
    /// Advance multiple slices by `n`, skipping and truncating slices until there are `n` less
    /// total bytes.
    ///
    /// They are always advanced from start to end, and only the last slice will actually be
    /// changed if the count turned out to be uneven. `None` is returned if `n` turns out to be
    /// greater than the total length of the slices, so that counting beforehand becomes
    /// unnecessary.
    #[must_use]
    #[inline]
    pub fn advance_within(mut slices: &mut [Self], mut n: usize) -> Option<&mut [Self]> {
        while let Some(buffer) = slices.first_mut() {
            if n == 0 {
                return Some(slices);
            };

            let buffer_len = buffer.len();

            if buffer_len > n {
                buffer.advance(n);
            } else {
                slices = &mut slices[1..];
            }
            n -= core::cmp::min(buffer_len, n);
        }
        if n > 0 {
            return None;
        }
        Some(slices)
    }
    /// Retrieve the "inner data" immutably, pointed to by the I/O slice, being to either `&[u8]`
    /// or `&[MaybeUninit<u8>]` depending on the generic type parameter `I`.
    #[inline]
    pub fn inner_data(&self) -> &[I::DerefTargetItem] {
        unsafe {
            core::slice::from_raw_parts(self.__ptr() as *const I::DerefTargetItem, self.__len())
        }
    }
    /// Retrieve the "inner data" mutably, pointed to by the I/O slice, being to either `&mut [u8]`
    /// or `&mut [MaybeUninit<u8>]` depending on the generic type parameter `I`.
    #[inline]
    pub fn inner_data_mut(&mut self) -> &mut [I::DerefTargetItem] {
        unsafe {
            core::slice::from_raw_parts_mut(self.__ptr() as *mut I::DerefTargetItem, self.__len())
        }
    }
    /// Get the "inner data" mutably, but with the lifetime `'a` rather than the lifetime of
    /// `self`.
    #[inline]
    pub fn into_inner_data(self) -> &'a mut [I::DerefTargetItem] {
        unsafe {
            core::slice::from_raw_parts_mut(self.__ptr() as *mut I::DerefTargetItem, self.__len())
        }
    }
    /// Convert a regular slice that points to either `u8` or `MaybeUninit<u8>`, into
    /// [`IoSliceMut`].
    #[inline]
    pub fn from_inner_data(inner_data: &'a mut [I::DerefTargetItem]) -> Self {
        unsafe { Self::__construct(inner_data.as_mut_ptr() as *mut u8, inner_data.len()) }
    }

    #[inline]
    pub fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        self.as_uninit().inner_data()
    }
    #[inline]
    pub fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_uninit_mut().inner_data_mut()
    }

    #[inline]
    #[must_use]
    pub fn zeroed(mut self) -> IoSliceMut<'a, Initialized> {
        #[cfg(feature = "nightly")]
        {
            self.as_maybe_uninit_slice_mut().fill(MaybeUninit::new(0));
        }

        #[cfg(not(feature = "nightly"))]
        {
            for byte in self.as_maybe_uninit_slice_mut() {
                *byte = MaybeUninit::new(0);
            }
        }

        unsafe { self.assume_init() }
    }
    #[inline]
    #[must_use]
    pub fn zeroed_by_ref<'b>(&'b mut self) -> &'b mut IoSliceMut<'a, Initialized> {
        #[cfg(feature = "nightly")]
        {
            self.as_maybe_uninit_slice_mut().fill(MaybeUninit::new(0));
        }

        #[cfg(not(feature = "nightly"))]
        {
            for byte in self.as_maybe_uninit_slice_mut() {
                *byte = MaybeUninit::new(0);
            }
        }

        unsafe { self.assume_init_mut() }
    }

    #[inline]
    fn __ptr(&self) -> *mut u8 {
        #[cfg(all(unix, feature = "libc"))]
        return self.inner.0.iov_base as *mut u8;

        #[cfg(all(windows, feature = "libc"))]
        return self.inner.0.buf as *mut u8;

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        return self.inner.as_ptr() as *mut u8;
    }
    #[inline]
    fn __len(&self) -> usize {
        #[cfg(all(unix, feature = "libc"))]
        return self.inner.0.iov_len as usize;

        #[cfg(all(windows, feature = "libc"))]
        return self.inner.0.len as usize;

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        return self.inner.len();
    }
    #[inline]
    unsafe fn __set_ptr(&mut self, ptr: *mut u8) {
        #[cfg(all(unix, feature = "libc"))]
        {
            self.inner.0.iov_base = ptr as *mut libc::c_void;
        }

        #[cfg(all(windows, feature = "winapi"))]
        {
            self.inner.0.buf = ptr as *mut CHAR;
        }

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        {
            self.inner =
                core::slice::from_raw_parts_mut(ptr as *mut I::DerefTargetItem, self.__len());
        }
    }
    #[inline]
    unsafe fn __set_len(&mut self, len: usize) {
        #[cfg(all(unix, feature = "libc"))]
        {
            self.inner.0.iov_len = len as usize;
        }

        #[cfg(all(windows, feature = "libc"))]
        {
            use core::convert::TryInto;

            self.inner.0.len = len
                .try_into()
                .expect("length exceeding 2^32 bytes, which is the limit of WSABUF");
        }

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        {
            self.inner =
                core::slice::from_raw_parts_mut(self.__ptr() as *mut I::DerefTargetItem, len);
        }
    }
    #[inline]
    unsafe fn __construct(ptr: *mut u8, len: usize) -> Self {
        #[cfg(all(windows, feature = "winapi"))]
        use core::convert::TryInto;

        Self {
            #[cfg(all(unix, feature = "libc"))]
            inner: (
                libc::iovec {
                    iov_base: ptr as *mut libc::c_void,
                    iov_len: len as usize,
                },
                PhantomData,
            ),
            #[cfg(all(windows, feature = "winapi"))]
            inner: (
                WSABUF {
                    len: len.try_into().expect(
                        "constructing an IoSlice that is larger than the 2^32 limits of WSABUF",
                    ),
                    buf: ptr as *mut CHAR,
                },
                PhantomData,
            ),
            #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
            inner: { core::slice::from_raw_parts_mut(ptr as *mut I::DerefTargetItem, len) },

            _marker: PhantomData,
        }
    }
}
impl<'a> IoSliceMut<'a, Initialized> {
    /// Retrieve the inner slice immutably. This requires the I/O slice to be initialized.
    ///
    /// Unlike the immutable [`IoSlice`], this will require a secondary lifetime of `self`, to
    /// prevent aliasing when the data can be mutated. If it is necessary to obtain a byte slice
    /// with lifetime `'a`, use [`to_slice`].
    ///
    /// [`to_slice`]: #method.to_slice
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        unsafe { cast_slice_same_layout(self.inner_data()) }
    }
    /// Take an [`IoSliceMut`] by value, turning it into an immutable byte slice of lifetime `'a`.
    #[inline]
    pub fn into_slice(self) -> &'a [u8] {
        &*self.into_slice_mut()
    }

    /// Retrieve the inner slice mutably. This requires the I/O slice to be initialized.
    ///
    /// Note that unlike [`into_slice_mut`], this will have the lifetime of `self`, not `'a`.
    ///
    /// [`into_slice_mut`]: #method.into_slice_mut
    #[inline]
    pub fn as_slice_mut(&mut self) -> &mut [u8] {
        unsafe { cast_slice_same_layout_mut(self.inner_data_mut()) }
    }

    /// Take an [`IoSliceMut`] by value, turning it into a mutable byte slice of lifetime `'a`.
    #[inline]
    pub fn into_slice_mut(self) -> &'a mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.__ptr(), self.__len()) }
    }

    // TODO: conversion by reference between std I/O slices

    /// Cast `&[IoSliceMut]` to `&[std::io::IoSlice]`.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_ioslices<'b>(slices: &'b [Self]) -> &'b [std::io::IoSlice<'a>] {
        unsafe { cast_slice_same_layout(slices) }
    }

    /// Cast `&[IoSliceMut]` to `&[std::io::IoSliceMut]`.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_mut_ioslices<'b>(slices: &'b [Self]) -> &'b [std::io::IoSliceMut<'a>] {
        unsafe { cast_slice_same_layout(slices) }
    }
    /// Cast `&mut [IoSliceMut]` to `&mut [std::io::IoSlice]`.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_ioslices_mut<'b>(slices: &'b mut [Self]) -> &'b mut [std::io::IoSlice<'a>] {
        unsafe { cast_slice_same_layout_mut(slices) }
    }

    /// Cast `&mut [IoSliceMut]` to `&mut [std::io::IoSliceMut]`.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_mut_ioslices_mut(
        slices: &'a mut [Self],
    ) -> &'a mut [std::io::IoSliceMut<'a>] {
        unsafe { cast_slice_same_layout_mut(slices) }
    }
}

impl<'a, I: Initialization> AsRef<[I::DerefTargetItem]> for IoSliceMut<'a, I> {
    #[inline]
    fn as_ref(&self) -> &[I::DerefTargetItem] {
        self.inner_data()
    }
}
impl<'a, I: Initialization> Borrow<[I::DerefTargetItem]> for IoSliceMut<'a, I> {
    #[inline]
    fn borrow(&self) -> &[I::DerefTargetItem] {
        self.inner_data()
    }
}
impl<'a, I: Initialization> ops::Deref for IoSliceMut<'a, I> {
    type Target = [I::DerefTargetItem];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner_data()
    }
}
impl<'a, I: Initialization> AsMut<[I::DerefTargetItem]> for IoSliceMut<'a, I> {
    #[inline]
    fn as_mut(&mut self) -> &mut [I::DerefTargetItem] {
        self.inner_data_mut()
    }
}
impl<'a, I: Initialization> BorrowMut<[I::DerefTargetItem]> for IoSliceMut<'a, I> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [I::DerefTargetItem] {
        self.inner_data_mut()
    }
}
impl<'a, I: Initialization> ops::DerefMut for IoSliceMut<'a, I> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner_data_mut()
    }
}
#[cfg(all(unix, feature = "libc"))]
impl<'a, I: Initialization> From<IoSliceMut<'a, I>> for libc::iovec {
    #[inline]
    fn from(slice: IoSliceMut<'a, I>) -> Self {
        slice.as_raw_iovec()
    }
}

impl<'a, I: Initialization> fmt::Debug for IoSliceMut<'a, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if I::IS_INITIALIZED {
            write!(f, "{:?}", self.inner_data())
        } else {
            write!(
                f,
                "[possibly uninitialized mutable I/O slice at {:p}, len {} bytes]",
                self.as_maybe_uninit_slice().as_ptr(),
                self.as_maybe_uninit_slice().len()
            )
        }
    }
}
impl<'a> PartialEq for IoSliceMut<'a, Initialized> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}
impl<'a> PartialEq<[u8]> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}
impl<'a, 'b> PartialEq<IoSlice<'b, Initialized>> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn eq(&self, other: &IoSlice<'b>) -> bool {
        self.as_slice() == other.as_slice()
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialEq<[u8; N]> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn eq(&self, other: &[u8; N]) -> bool {
        self.as_slice() == &other[..]
    }
}
impl<'a> Eq for IoSliceMut<'a, Initialized> {}

impl<'a> PartialOrd for IoSliceMut<'a, Initialized> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}
impl<'a> PartialOrd<[u8]> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn partial_cmp(&self, other: &[u8]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}
impl<'a, 'b> PartialOrd<IoSlice<'b, Initialized>> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn partial_cmp(&self, other: &IoSlice<'b, Initialized>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other.as_slice())
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialOrd<[u8; N]> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn partial_cmp(&self, other: &[u8; N]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}
impl<'a> Ord for IoSliceMut<'a, Initialized> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(self.as_slice(), other.as_slice())
    }
}
impl<'a> hash::Hash for IoSliceMut<'a, Initialized> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        state.write(self.as_slice())
    }
}
impl<'a, I: Initialization> From<&'a mut [I::DerefTargetItem]> for IoSliceMut<'a, I> {
    #[inline]
    fn from(slice: &'a mut [I::DerefTargetItem]) -> Self {
        Self::from_inner_data(slice)
    }
}
impl<'a> From<&'a mut [u8]> for IoSliceMut<'a, Uninitialized> {
    #[inline]
    fn from(slice: &'a mut [u8]) -> Self {
        Self::new(slice)
    }
}
#[cfg(feature = "nightly")]
impl<'a, I: Initialization, const N: usize> From<&'a mut [I::DerefTargetItem; N]>
    for IoSliceMut<'a, I>
{
    #[inline]
    fn from(slice: &'a mut [I::DerefTargetItem; N]) -> Self {
        Self::from_inner_data(slice)
    }
}

#[cfg(feature = "stable_deref_trait")]
unsafe impl<'a> stable_deref_trait::StableDeref for IoSliceMut<'a> {}

#[cfg(all(unix, feature = "alloc"))]
mod io_box {
    use super::*;

    use alloc::alloc::{
        alloc as allocate, alloc_zeroed as allocate_zeroed, dealloc as deallocate, Layout,
    };
    use alloc::boxed::Box;
    use alloc::vec::Vec;

    /// An owned chunk of memory, that is ABI-compatible with [`libc::iovec`]. At the moment this
    /// does not work on Windows.
    ///
    /// This must be allocated via the system alloc; importing pointers from _malloc(2)_ is
    /// currently not possible.
    #[repr(transparent)]
    pub struct IoBox<I: Initialization = Initialized> {
        #[cfg(all(unix, feature = "libc"))]
        inner: libc::iovec,

        #[cfg(not(all(unix, feature = "libc")))]
        inner: Box<[I::DerefTargetItem]>,

        _marker: PhantomData<I>,
    }
    /// An error that may occur if allocating an I/O box fails.
    ///
    /// This will most likely never occur on real operating systems, but being able to handle this
    /// error is crucial when working in resource-limited environments, or in e.g. OS kernels.
    pub struct AllocationError(Layout);

    impl AllocationError {
        /// Retrieve the layout that the allocator failed to allocate.
        pub fn layout(&self) -> &Layout {
            &self.0
        }
    }

    impl<I: Initialization> IoBox<I> {
        // TODO: While really niche (except maybe for O_DIRECT where buffers need to be
        // page-aligned?), one should also be able to directly specify a layout.

        #[inline]
        fn try_alloc_inner<J: Initialization>(
            length: usize,
            zeroed: bool,
        ) -> Result<IoBox<J>, AllocationError> {
            let layout = Layout::from_size_align(
                mem::size_of::<u8>()
                    .checked_mul(length)
                    .expect("overflow when multiplying length with size of u8"),
                mem::align_of::<u8>(),
            )
            .expect("error when creating allocation layout");

            let pointer = match zeroed {
                false => unsafe { allocate(layout) },
                true => unsafe { allocate_zeroed(layout) },
            };

            if pointer.is_null() {
                return Err(AllocationError(layout));
            }

            Ok(unsafe { IoBox::from_raw_parts(pointer as *mut J::DerefTargetItem, length) })
        }
        /// Attempt to allocate `length` bytes, which are initially set to zero.
        ///
        /// This allocation may fail, but should not be used unless the global allocator actually
        /// does return null when there is no memory. This is generally not the case for userspace
        /// processes, where the kernel gives more memory than physically available, but is
        /// obviously useful in `#![no_std]`.
        ///
        /// Since the allocator may be able to already have zeroed blocks of memory, this should be
        /// preferred over manually initializing it using [`zeroed`].
        ///
        /// [`zeroed`]: #method.zeroed
        #[inline]
        pub fn try_alloc_zeroed(length: usize) -> Result<Self, AllocationError> {
            Self::try_alloc_inner(length, true)
        }

        /// Allocate `length` bytes, which are initially set to zero.
        ///
        /// # Panics
        ///
        /// This method will, like most other heap-allocated structures in the `alloc` crate, panic
        /// when there is no available memory left.
        #[inline]
        pub fn alloc_zeroed(length: usize) -> Self {
            match Self::try_alloc_zeroed(length) {
                Ok(boxed) => boxed,
                Err(AllocationError(layout)) => alloc::alloc::handle_alloc_error(layout),
            }
        }

        /// Turn the I/O box into the underlying pointer and size.
        #[inline]
        pub fn into_raw_parts(self) -> (*mut u8, usize) {
            #[cfg(all(unix, feature = "libc"))]
            return {
                let iov_base = self.inner.iov_base as *mut u8;
                let iov_len = self.inner.iov_len;

                core::mem::forget(self);

                (iov_base, iov_len)
            };
            #[cfg(not(all(unix, feature = "libc")))]
            return {
                let slice_ptr = self.inner.into_raw();

                unsafe {
                    let slice = &*slice_ptr;
                    (slice.as_mut_ptr(), slice.len())
                }
            };
        }
        /// Convert an underlying pointer and size, into an [`IoBox`].
        ///
        /// # Safety
        ///
        /// For this to be safe, the validity and initialization invariants must be held. In
        /// addition to that, the pointer must be allocated using the system allocator.
        #[inline]
        pub unsafe fn from_raw_parts(base: *mut I::DerefTargetItem, len: usize) -> Self {
            #[cfg(all(unix, feature = "libc"))]
            return {
                Self {
                    inner: libc::iovec {
                        iov_base: base as *mut libc::c_void,
                        iov_len: len,
                    },
                    _marker: PhantomData,
                }
            };

            #[cfg(not(all(unix, feature = "libc")))]
            return {
                Self {
                    inner: Box::from_raw(core::slice::from_raw_parts_mut(base, len)),
                    _marker: PhantomData,
                }
            };
        }
        #[cfg(all(unix, feature = "libc"))]
        pub fn into_iovec(self) -> libc::iovec {
            let iovec = self.inner;
            core::mem::forget(self);
            iovec
        }

        pub fn into_box(self) -> Box<[I::DerefTargetItem]> {
            #[cfg(all(unix, feature = "libc"))]
            return {
                let (ptr, len) = self.into_raw_parts();
                unsafe {
                    Box::from_raw(core::slice::from_raw_parts_mut(
                        ptr as *mut I::DerefTargetItem,
                        len,
                    ))
                }
            };

            #[cfg(not(all(unix, feature = "libc")))]
            return { io_box.inner };
        }
        pub fn as_ioslice(&self) -> IoSlice<I> {
            IoSlice::from_inner_data(self.inner_data())
        }
        pub fn as_ioslice_mut(&mut self) -> IoSliceMut<I> {
            IoSliceMut::from_inner_data(self.inner_data_mut())
        }
        pub fn inner_data(&self) -> &[I::DerefTargetItem] {
            #[cfg(all(unix, feature = "libc"))]
            return unsafe {
                core::slice::from_raw_parts(
                    self.inner.iov_base as *const I::DerefTargetItem,
                    self.inner.iov_len,
                )
            };

            #[cfg(not(all(unix, feature = "libc")))]
            return &*self.inner;
        }
        pub fn inner_data_mut(&mut self) -> &mut [I::DerefTargetItem] {
            #[cfg(all(unix, feature = "libc"))]
            return unsafe {
                core::slice::from_raw_parts_mut(
                    self.inner.iov_base as *mut I::DerefTargetItem,
                    self.inner.iov_len,
                )
            };

            #[cfg(not(all(unix, feature = "libc")))]
            return &mut *self.inner;
        }
        #[inline]
        pub fn cast_to_ioslices(these: &[Self]) -> &[IoSlice<I>] {
            unsafe { cast_slice_same_layout(these) }
        }
        #[inline]
        pub unsafe fn cast_to_ioslices_mut(these: &mut [Self]) -> &mut [IoSlice<I>] {
            cast_slice_same_layout_mut(these)
        }
        #[inline]
        pub fn cast_to_mut_ioslices(these: &[Self]) -> &[IoSliceMut<I>] {
            unsafe { cast_slice_same_layout(these) }
        }
        #[inline]
        pub unsafe fn cast_to_mut_ioslices_mut(these: &mut [Self]) -> &mut [IoSliceMut<I>] {
            cast_slice_same_layout_mut(these)
        }
        /// Convert `IoBox<_>` into `IoBox<Initialized>`, assuming that the data is initialized.
        ///
        /// # Safety
        ///
        /// __This shall not be used for initializing data. In that case, initialize it manually
        /// via [`as_maybe_uninit_slice_mut`], and then call this.__
        ///
        /// While the validity invariant is already upheld when creating this type, the caller must
        /// ensure that the data be initialized. Refer to the [`std::mem::MaybeUninit`] docs.
        ///
        /// [`as_maybe_uninit_slice_mut`]: #method.as_maybe_uninit_slice_mut
        #[inline]
        pub unsafe fn assume_init(self) -> IoBox<Initialized> {
            IoBox {
                inner: self.inner,
                _marker: PhantomData,
            }
        }
        #[inline]
        pub fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
            unsafe { cast_slice_same_layout(self.inner_data()) }
        }
        #[inline]
        pub fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
            unsafe { cast_slice_same_layout_mut(self.inner_data_mut()) }
        }

        pub fn zeroed(mut self) -> IoBox<Initialized> {
            #[cfg(feature = "nightly")]
            {
                self.as_maybe_uninit_slice_mut().fill(MaybeUninit::new(0u8));
            }
            #[cfg(not(feature = "nightly"))]
            {
                for byte in self.as_maybe_uninit_slice_mut() {
                    *byte = MaybeUninit::new(0u8);
                }
            }
            unsafe { self.assume_init() }
        }
        pub fn try_alloc_uninit(length: usize) -> Result<IoBox<Uninitialized>, AllocationError> {
            Self::try_alloc_inner(length, false)
        }
        pub fn alloc_uninit(length: usize) -> IoBox<Uninitialized> {
            match Self::try_alloc_uninit(length) {
                Ok(boxed) => boxed,
                Err(AllocationError(layout)) => alloc::alloc::handle_alloc_error(layout),
            }
        }
    }
    impl IoBox<Initialized> {
        pub fn as_slice(&self) -> &[u8] {
            self.inner_data()
        }
        pub fn as_slice_mut(&mut self) -> &mut [u8] {
            self.inner_data_mut()
        }
    }
    impl<I: Initialization> Drop for IoBox<I> {
        fn drop(&mut self) {
            #[cfg(all(unix, feature = "libc"))]
            unsafe {
                deallocate(
                    self.inner.iov_base as *mut u8,
                    Layout::from_size_align(
                        self.inner
                            .iov_len
                            .checked_mul(mem::size_of::<u8>())
                            .unwrap(),
                        mem::align_of::<u8>(),
                    )
                    .unwrap(),
                );
            }
        }
    }
    impl<I: Initialization> From<Box<[I::DerefTargetItem]>> for IoBox<I> {
        fn from(boxed: Box<[I::DerefTargetItem]>) -> Self {
            unsafe {
                let slice_ptr = Box::into_raw(boxed);

                // TODO: #![feature(slice_ptr_len)]
                //let iov_len = slice_ptr.len();

                let len = (&*slice_ptr).len();
                let base = (&*slice_ptr).as_ptr() as *mut I::DerefTargetItem;

                Self::from_raw_parts(base, len)
            }
        }
    }
    impl From<Box<[u8]>> for IoBox<Uninitialized> {
        fn from(boxed: Box<[u8]>) -> Self {
            unsafe {
                let slice_ptr = Box::into_raw(boxed);

                // TODO: #![feature(slice_ptr_len)]
                //let iov_len = slice_ptr.len();

                let len = (&*slice_ptr).len();
                let base = (&*slice_ptr).as_ptr() as *mut MaybeUninit<u8>;

                Self::from_raw_parts(base, len)
            }
        }
    }
    impl<I: Initialization> From<Vec<I::DerefTargetItem>> for IoBox<I> {
        fn from(vector: Vec<I::DerefTargetItem>) -> Self {
            Self::from(vector.into_boxed_slice())
        }
    }
    impl From<Vec<u8>> for IoBox<Uninitialized> {
        fn from(vector: Vec<u8>) -> Self {
            Self::from(vector.into_boxed_slice())
        }
    }
    impl From<IoBox> for Box<[u8]> {
        fn from(io_box: IoBox) -> Self {
            io_box.into_box()
        }
    }
    impl From<IoBox> for Vec<u8> {
        fn from(io_box: IoBox) -> Self {
            Self::from(Box::from(io_box))
        }
    }
    impl core::fmt::Debug for IoBox {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{:?}", self.as_slice())
        }
    }
    impl core::ops::Deref for IoBox {
        type Target = [u8];

        fn deref(&self) -> &[u8] {
            self.as_slice()
        }
    }
    impl core::ops::DerefMut for IoBox {
        fn deref_mut(&mut self) -> &mut [u8] {
            self.as_slice_mut()
        }
    }
    impl<I: Initialization> AsRef<[I::DerefTargetItem]> for IoBox<I> {
        fn as_ref(&self) -> &[I::DerefTargetItem] {
            self.inner_data()
        }
    }
    impl<I: Initialization> AsMut<[I::DerefTargetItem]> for IoBox<I> {
        fn as_mut(&mut self) -> &mut [I::DerefTargetItem] {
            self.inner_data_mut()
        }
    }
    impl core::borrow::Borrow<[u8]> for IoBox {
        fn borrow(&self) -> &[u8] {
            self.as_slice()
        }
    }
    impl core::borrow::BorrowMut<[u8]> for IoBox {
        fn borrow_mut(&mut self) -> &mut [u8] {
            self.as_slice_mut()
        }
    }
    impl PartialEq for IoBox {
        fn eq(&self, other: &Self) -> bool {
            self.as_slice() == other.as_slice()
        }
    }
    impl PartialEq<[u8]> for IoBox {
        fn eq(&self, other: &[u8]) -> bool {
            self.as_slice() == other
        }
    }
    impl<'a> PartialEq<IoSlice<'a>> for IoBox {
        fn eq(&self, other: &IoSlice) -> bool {
            self.as_slice() == other.as_slice()
        }
    }
    impl<'a> PartialEq<IoSliceMut<'a>> for IoBox {
        fn eq(&self, other: &IoSliceMut) -> bool {
            self.as_slice() == other.as_slice()
        }
    }
    impl Eq for IoBox {}
    // TODO: more impls
}
#[cfg(all(unix, feature = "alloc"))]
pub use io_box::*;

#[cfg(test)]
mod tests {
    use super::*;

    const FIRST: &[u8] = b"this";
    const SECOND: &[u8] = b"is";
    const THIRD: &[u8] = b"FAL";
    const FOURTH: &[u8] = b"-rs";
    const SPACE: &[u8] = b" ";

    #[test]
    fn advance() {
        let original_slices = [FIRST, SPACE, SECOND, SPACE, THIRD, FOURTH];
        let mut original_ioslices = original_slices
            .iter()
            .copied()
            .map(|slice| IoSlice::from(slice))
            .collect::<Vec<_>>();

        let original_slices = &original_slices[..];
        let original_ioslices = &mut original_ioslices[..];

        fn check_slices(ioslices: &[IoSlice], slice: &[&[u8]]) {
            assert!(ioslices
                .iter()
                .map(|ioslice| ioslice.as_slice())
                .eq(slice.iter().copied()));
        }

        let mut ioslices = original_ioslices;

        check_slices(ioslices, original_slices);

        ioslices = IoSlice::advance_within(ioslices, 0).unwrap();
        check_slices(ioslices, &[b"this", b" ", b"is", b" ", b"FAL", b"-rs"]);

        ioslices = IoSlice::advance_within(ioslices, 2).unwrap();
        check_slices(ioslices, &[b"is", b" ", b"is", b" ", b"FAL", b"-rs"]);

        ioslices = IoSlice::advance_within(ioslices, 5).unwrap();
        check_slices(ioslices, &[b" ", b"FAL", b"-rs"]);

        ioslices = IoSlice::advance_within(ioslices, 6).unwrap();
        check_slices(ioslices, &[b"s"]);

        ioslices = IoSlice::advance_within(ioslices, 1).unwrap();
        check_slices(ioslices, &[]);

        assert_eq!(IoSlice::advance_within(ioslices, 1), None);
    }

    #[test]
    #[cfg(feature = "std")]
    fn abi_compatibility_with_std() {
        assert_eq!(
            mem::size_of::<IoSlice>(),
            mem::size_of::<std::io::IoSlice>()
        );
        assert_eq!(
            mem::align_of::<IoSlice>(),
            mem::align_of::<std::io::IoSlice>()
        );

        let slices = [FIRST, SECOND, THIRD, FOURTH];
        let mut ioslices = [
            IoSlice::new(FIRST),
            IoSlice::new(SECOND),
            IoSlice::new(THIRD),
            IoSlice::new(FOURTH),
        ];
        let std_ioslices = IoSlice::cast_to_std_ioslices(&ioslices);

        assert!(std_ioslices
            .iter()
            .map(|ioslice| ioslice.as_ref())
            .eq(slices.iter().copied()));

        use std::io::prelude::*;

        let mut buffer =
            vec![0u8; slices.iter().copied().map(<[u8]>::len).sum()].into_boxed_slice();

        let mut total = 0;

        let mut ioslices = &mut ioslices[..];

        loop {
            let std_ioslices = IoSlice::cast_to_std_ioslices(&ioslices);

            match (&mut *buffer).write_vectored(std_ioslices) {
                Ok(0) => break,
                Ok(n) => {
                    ioslices = IoSlice::advance_within(ioslices, n).unwrap();
                    total += n
                }
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(error) => Err(error).unwrap(),
            }
        }
        assert_eq!(total, buffer.len());
        assert_eq!(&*buffer, b"thisisFAL-rs");
    }
    #[test]
    #[cfg(all(unix, feature = "libc"))]
    fn abi_compatibility_with_iovec() {
        use std::convert::TryInto;

        assert_eq!(mem::size_of::<IoSlice>(), mem::size_of::<libc::iovec>());
        assert_eq!(mem::align_of::<IoSlice>(), mem::align_of::<libc::iovec>());

        unsafe {
            let slice: &[u8] = b"Hello, world!";

            let iov_base = slice.as_ptr() as *mut libc::c_void;
            let iov_len = slice.len();

            let vec = libc::iovec { iov_base, iov_len };

            let wrapped: IoSlice = mem::transmute::<libc::iovec, IoSlice>(vec);
            assert_eq!(wrapped.as_ptr(), iov_base as *const u8);
            assert_eq!(wrapped.len(), iov_len);
        }

        let ioslices = [
            IoSlice::new(FIRST),
            IoSlice::new(SPACE),
            IoSlice::new(SECOND),
            IoSlice::new(SPACE),
            IoSlice::new(THIRD),
            IoSlice::new(FOURTH),
        ];
        let iovecs = IoSlice::cast_to_raw_iovecs(&ioslices);

        let mut fds = [0; 2];

        unsafe {
            libc::pipe(fds.as_mut_ptr());
        }
        let [receiver_fd, sender_fd] = fds;

        let mut buffer = vec![0u8; ioslices.iter().map(|slice| slice.len()).sum()];
        let buffer_parts = buffer
            .chunks_mut(4)
            .map(|slice| IoSliceMut::new(slice))
            .collect::<Vec<_>>();
        let buffer_parts_iovecs = IoSliceMut::cast_to_raw_iovecs(&*buffer_parts);

        unsafe {
            // TODO: Maybe repeat since writev and readv don't have to return everything?
            let result = libc::writev(sender_fd, iovecs.as_ptr(), iovecs.len().try_into().unwrap());

            if result == -1 {
                panic!("failed to writev: {}", std::io::Error::last_os_error());
            }

            let result = libc::readv(
                receiver_fd,
                buffer_parts_iovecs.as_ptr(),
                buffer_parts_iovecs.len().try_into().unwrap(),
            );

            if result == -1 {
                panic!("failed to readv: {}", std::io::Error::last_os_error());
            }
        }
        let src_iter = ioslices
            .iter()
            .flat_map(|ioslice| ioslice.as_slice())
            .copied();
        let dst_iter = buffer_parts
            .iter()
            .flat_map(|ioslice| ioslice.as_slice())
            .copied();
        assert!(Iterator::eq(src_iter, dst_iter));
    }
    // TODO: Make IoSlice compatible with WSABUF without std as well.
}

#[inline]
unsafe fn cast_slice_same_layout<A, B>(a: &[A]) -> &[B] {
    core::slice::from_raw_parts(a.as_ptr() as *const B, a.len())
}
#[inline]
unsafe fn cast_slice_same_layout_mut<A, B>(a: &mut [A]) -> &mut [B] {
    core::slice::from_raw_parts_mut(a.as_mut_ptr() as *mut B, a.len())
}

/// Cast a slice of bytes into a slice of uninitialized bytes, pretending that it is uninitialized.
/// This is completely safe, since `MaybeUninit` must have the exact same (direct) layout, like
/// `u8` has. The downside with this is that the information about initializedness is lost; unless
/// relying on unsafe code, the resulting slice can only be used to prove validity of the memory
/// range.
#[inline]
pub fn cast_init_to_uninit_slice(init: &[u8]) -> &[MaybeUninit<u8>] {
    unsafe { cast_slice_same_layout(init) }
}
/// Cast a possibly uninitialized slice of bytes, into an initializied slice, assuming that it is
/// initialized.
///
/// # Safety
///
/// The initialization variant must be upheld; that is, the caller must ensure that the buffer
/// cannot contain any uninitialized data.
#[inline]
pub unsafe fn cast_uninit_to_init_slice(uninit: &[MaybeUninit<u8>]) -> &[u8] {
    cast_slice_same_layout(uninit)
}

/// Cast a mutable slice of bytes into a slice of uninitialized bytes, pretending that it is
/// uninitialized. This is completely safe since they always have the same memory layout; however,
/// the layout of the slices themselves must not be relied upon. The initializedness information is
/// lost as part of this cast, but can be recovered when initializing again or by using unsafe
/// code.
#[inline]
pub fn cast_init_to_uninit_slice_mut(init: &mut [u8]) -> &mut [MaybeUninit<u8>] {
    unsafe { cast_slice_same_layout_mut(init) }
}
/// Cast a mutable slice of possibly initialized bytes into a slice of initialized bytes, assuming
/// it is initialized.
///
/// # Safety
///
/// For this to be safe, the initialization invariant must be upheld, exactly like when reading.
///
/// __This must not be used for initializing the buffer. For that, there are are other safe methods
/// like [`init_from_slice`] and [`init_by_filling`]. If unsafe code is still somehow, always initialize this by
/// copying from _another_ MaybeUninit slice, or using [`std::ptr::copy`] or
/// [`std::ptr::copy_nonoverlapping`].__
#[inline]
pub unsafe fn cast_uninit_to_init_slice_mut(uninit: &mut [MaybeUninit<u8>]) -> &mut [u8] {
    cast_slice_same_layout_mut(uninit)
}
