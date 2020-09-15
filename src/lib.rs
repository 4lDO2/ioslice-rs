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
//!
//! # Examples
//!
//! ## A `Read`-like trait implemented to better support uninitialized memory.
//! ```
//! # use std::io;
//!
//! use std::mem::MaybeUninit;
//!
//! use ioslice::{Initialization, Initialized, IoSliceMut, SliceMutPartialExt};
//! # // TODO: Add more safe abstractions for slices of I/O slices.
//!
//! pub trait MyRead {
//!     // NOTE: This could be a regular slice as well.
//!     fn read<'a, I: Initialization>(&mut self, slice: IoSliceMut<'a, I>) ->
//!     io::Result<(IoSliceMut<'a, Initialized>, IoSliceMut<'a, I>)>;
//! }
//!
//! impl MyRead for &[u8] {
//!     fn read<'a, I: Initialization>(&mut self, slice: IoSliceMut<'a, I>) ->
//!     io::Result<(IoSliceMut<'a, Initialized>, IoSliceMut<'a, I>)> {
//!         // Begin with taking the minimum slice that can fit the copy into the buffer.
//!         let bytes_to_copy = std::cmp::min(self.len(), slice.len());
//!         let (source, source_remainder) = self.split_at(bytes_to_copy);
//!
//!         // Split the possibly uninitialized slice into an initialized and an uninitialized
//!         // part. This allows the `Read` implementation to only read part of the data requested.
//!         //
//!         // Normally this would be done via returning `usize`, but we need to be able to prove
//!         // that we have initialized it.
//!         let (initialized, remainder) = slice.partially_init_by_copying(source);
//!
//!         // Advance the slice that is being read.
//!         let bytes_copied = initialized.len();
//!         *self = source_remainder;
//!
//!         // And finally, return the initialized part and the remainder to prove that we have
//!         // initialized it. (And to make it possible for safe code to use the buffer directly.)
//!         Ok((initialized, remainder))
//!     }
//! }
//!
//! # fn main() -> io::Result<()> {
//!
//! let mut buf = [MaybeUninit::uninit(); 32];
//! let buf = IoSliceMut::from_uninit(&mut buf);
//! let len = buf.len();
//!
//! let original_stupid_text: &[u8] = b"copying is expensive!";
//! let mut stupid_text = original_stupid_text;
//!
//! // Read as many bytes as possible.
//! let (initialized, remainder) = stupid_text.read(buf)?;
//! assert_eq!(initialized, original_stupid_text);
//!
//! // Note that while we cannot read the rest of the buffer, we can still use it as the
//! // destination of even more I/O, or simply check its length here.
//! assert_eq!(remainder.len(), len - original_stupid_text.len());
//!
//! # Ok(())
//!
//! # }
//!
//! ```
//!
//! Note that this may not be the best implementation of the `Read` trait, but it does show that
//! uninitialized memory handling can be done entirely in safe code, being moderately ergonomic.
//!
//! (If this would be incorporated into `std::io::Read`, there would probably be a simpler unsafe
//! function, that defaults to the safer wrapper.)

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
    /// Wrap a system `WSABUF` into a wrapped I/O slice, assuming the buffer can be represented as
    /// borrowed for the lifetime `'a`. Consider wrapping it in an [`IoBox`] if ownership of the
    /// `WSABUF` is desired.
    ///
    /// # Safety
    ///
    /// For this to be safe, the slice must be _valid_ (refer to the [`std::ptr`] docs) and not
    /// aliased mutably. If the generic parameter `I` is set to `Initialized`, the slice must also
    /// contain initialized data.
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub unsafe fn from_raw_wsabuf(slice: WSABUF) -> Self {
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

    /// Retrieve the inner WSABUF from this I/O slice.
    ///
    /// The raw WSABUF must be considered borrowed from this slice, even though it is not
    /// explicitly tracked using a lifetime.
    ///
    /// _This is only available on Windows targets with the `winapi` feature enabled._
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub fn as_raw_wsabuf(&self) -> WSABUF {
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

    /// Cast a slice of I/O slices into a slice of `WSABUF`s. Since these must share the same ABI
    /// layout, this is completely safe, and the resulting slice can directly be passed to system
    /// calls.
    ///
    /// _This is only available on Windows targets with the `winapi` feature enabled_.
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub fn cast_to_raw_wsabufs(slices: &'a [Self]) -> &'a [WSABUF] {
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
    /// Cast a mutable slice of I/O slices into a mutable slice of `WSABUF`s. Those share the exact
    /// same ABI guarantees as this wrapper does.
    ///
    /// _This is only available on WIndows targets with the `winapi` feature enabled_.
    ///
    /// # Safety
    ///
    /// This is unsafe, since the `WSABUF`s can be mutated entirely in safe code, which will cause
    /// the original wrapped slices to be changed as well. If the buffers are changed to invalid
    /// values in any way, this breaks the validity invariant upheld by this wrapped type, leading
    /// to UB.
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub unsafe fn cast_to_raw_wsabufs_mut(slices: &'a mut [Self]) -> &'a mut [WSABUF] {
        cast_slice_same_layout_mut(slices)
    }

    // TODO: from_raw_{iovec,wsabuf}s{,_mut}

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

    #[inline]
    pub fn split_at(self, mid: usize) -> (Self, Self) {
        let (a, b) = self.inner_data().split_at(mid);
        (Self::from_inner_data(a), Self::from_inner_data(b))
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
impl<'a, I: Initialization> AsRef<[MaybeUninit<u8>]> for IoSlice<'a, I> {
    #[inline]
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        self.as_maybe_uninit_slice()
    }
}
impl<'a> AsRef<[u8]> for IoSlice<'a, Initialized> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}
impl<'a, I: Initialization> Borrow<[I::DerefTargetItem]> for IoSlice<'a, I> {
    #[inline]
    fn borrow(&self) -> &[I::DerefTargetItem] {
        self.inner_data()
    }
}
impl<'a> Borrow<[MaybeUninit<u8>]> for IoSlice<'a, Initialized> {
    #[inline]
    fn borrow(&self) -> &[MaybeUninit<u8>] {
        self.as_maybe_uninit_slice()
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
    #[inline]
    pub fn as_uninit(&self) -> &IoSliceMut<'a, Uninitialized> {
        unsafe { &*(self as *const Self as *const IoSliceMut<'a, Uninitialized>) }
    }
    /// Cast an I/O slice, being [`Initialized`] or not, into an [`Uninitialized`] I/O slice, by
    /// mutable reference.
    #[inline]
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
    /// Wrap a system `WSABUF` into this wrapper.
    ///
    /// _This is only available on Windows targets with the `winapi` feature enabled._
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub unsafe fn from_raw_wsabuf(slice: WSABUF) -> Self {
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

    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub fn as_raw_wsabuf(&self) -> WSABUF {
        self.inner.0
    }
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub fn as_raw_wsabuf_mut(&mut self) -> WSABUF {
        self.inner.0
    }

    /// Cast a slice of wrapped I/O slices into a slice of [`libc::iovec`]s.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub fn cast_to_raw_iovecs(slices: &[Self]) -> &[libc::iovec] {
        unsafe { cast_slice_same_layout(slices) }
    }
    /// Cast a slice of wrapped I/O slices into a slice of `WSABUF`s.
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub fn cast_to_raw_wsabufs(slices: &[Self]) -> &[WSABUF] {
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
    /// Unsafely cast a mutable slice of wrapped I/O slices into a mutable slice of
    /// `WSABUF`s.
    ///
    /// # Safety
    ///
    /// This is unsafe because the initialization or validity invariants may be broken since the
    /// WSABUFs can be changed arbitrarily in a mutable reference.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub unsafe fn cast_to_raw_wsabufs_mut(slices: &mut [Self]) -> &mut [WSABUF] {
        cast_slice_same_layout_mut(slices)
    }

    /// Unsafely cast a slice of [`libc::iovec`]s into a slice of [`IoSliceMut`].
    ///
    /// _This is only available on Unix platforms with the `libc` feature enabled._
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
    /// _This is only available on Unix platforms with the `libc` feature enabled._
    ///
    /// # Safety
    ///
    /// This is unsafe since the iovecs must uphold the validity and initialization invariants.
    #[cfg(all(unix, feature = "libc"))]
    #[inline]
    pub unsafe fn from_raw_iovecs_mut(slice: &mut [libc::iovec]) -> &mut [Self] {
        cast_slice_same_layout_mut(slice)
    }
    /// Unsafely cast a slice of `WSABUF`s into a slice of [`IoSliceMut`].
    ///
    /// _This is only available on Windows platforms with the `winapi` feature enabled._
    ///
    /// # Safety
    ///
    /// This is unsafe since the buffers must uphold the validity and initialization invariants.
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub unsafe fn from_raw_wsabufs(slice: &[WSABUF]) -> &[Self] {
        cast_slice_same_layout(slice)
    }
    /// Unsafely cast a mutable slice of `WSABUF`s into a mutable slice of [`IoSliceMut`].
    ///
    /// _This is only available on Windows platforms with the `winapi` feature enabled._
    ///
    /// # Safety
    ///
    /// This is unsafe since the buffers must uphold the validity and initialization invariants.
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub unsafe fn from_raw_wsabufs_mut(slice: &mut [WSABUF]) -> &mut [Self] {
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
    #[inline]
    pub fn split_at(self, mid: usize) -> (Self, Self) {
        let (a, b) = self.into_inner_data().split_at_mut(mid);
        (Self::from_inner_data(a), Self::from_inner_data(b))
    }
}
impl<'a> IoSliceMut<'a, Uninitialized> {
    /// Create an uninitialized mutable I/O slice from a regular uninitialized mutable byte slice.
    pub fn from_uninit(uninit: &'a mut [MaybeUninit<u8>]) -> Self {
        Self::from_inner_data(uninit)
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
impl<'a> AsRef<[MaybeUninit<u8>]> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        self.as_maybe_uninit_slice()
    }
}
// TODO: Use #![feature(specialization)] and make sure that there is always an AsRef and Borrow
// impl for MaybeUninit and u8 regardless of the generic parameter.
// TODO: What about #![feature(const_generics)] and use an exhaustive enum for the type markers?
impl<'a, I: Initialization> Borrow<[MaybeUninit<u8>]> for IoSliceMut<'a, I> {
    #[inline]
    fn borrow(&self) -> &[MaybeUninit<u8>] {
        self.as_maybe_uninit_slice()
    }
}
impl<'a> Borrow<[u8]> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}
impl<'a, I: Initialization> ops::Deref for IoSliceMut<'a, I> {
    type Target = [I::DerefTargetItem];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner_data()
    }
}
impl<'a> AsMut<[u8]> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_slice_mut()
    }
}
impl<'a, I: Initialization> AsMut<[MaybeUninit<u8>]> for IoSliceMut<'a, I> {
    #[inline]
    fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_maybe_uninit_slice_mut()
    }
}
impl<'a, I: Initialization> BorrowMut<[MaybeUninit<u8>]> for IoSliceMut<'a, I> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_maybe_uninit_slice_mut()
    }
}
impl<'a> BorrowMut<[u8]> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [u8] {
        self.as_slice_mut()
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
impl<'a, 'b> PartialEq<&'b [u8]> for IoSliceMut<'a, Initialized> {
    #[inline]
    fn eq(&self, other: &&'b [u8]) -> bool {
        self.as_slice() == *other
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

#[cfg(feature = "alloc")]
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

        #[cfg(all(windows, feature = "winapi"))]
        inner: WSABUF,

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
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
        #[inline]
        pub fn layout(&self) -> &Layout {
            &self.0
        }
    }

    impl<I: Initialization> IoBox<I> {
        // TODO: While really niche (except maybe for O_DIRECT where buffers need to be
        // page-aligned?), one should also be able to directly specify a layout.

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

            #[cfg(all(windows, feature = "winapi"))]
            if length > u32::MAX as usize {
                panic!("IoBox (or any WSABUF-based I/O slice) cannot be larger in size than ULONG, which is 32 bits on Windows.");
            }

            let pointer = match zeroed {
                false => unsafe { allocate(layout) },
                true => unsafe { allocate_zeroed(layout) },
            };

            if pointer.is_null() {
                return Err(AllocationError(layout));
            }

            Ok(unsafe { IoBox::__construct(pointer as *mut J::DerefTargetItem, length) })
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
        /// # Panics
        ///
        /// This associated function will panic on Windows platforms when using the `winapi`
        /// feature, if the length exceeds the `WSABUF` limit of 2^32 bytes. Always check
        /// beforehand; this will never be returned as a regular allocation error.
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
        /// This associated function will, like most other heap-allocated structures in the `alloc`
        /// crate, panic when there is no available memory left. On Windows platforms with using
        /// the `winapi` feature, this will also panic if the length exceeds the `WSABUF` limit of
        /// 2^32 bytes.
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
            let ptr = self.__ptr();
            let len = self.__len();
            core::mem::forget(self);
            (ptr as *mut u8, len)
        }
        /// Convert an underlying pointer and size, into an [`IoBox`].
        ///
        /// # Safety
        ///
        /// For this to be safe, the validity and initialization invariants must be held. In
        /// addition to that, the pointer must be allocated using the system allocator.
        #[inline]
        pub unsafe fn from_raw_parts(base: *mut I::DerefTargetItem, len: usize) -> Self {
            Self::__construct(base, len)
        }
        #[cfg(all(unix, feature = "libc"))]
        pub fn into_raw_iovec(self) -> libc::iovec {
            let iovec = self.inner;
            core::mem::forget(self);
            iovec
        }
        #[cfg(all(windows, feature = "winapi"))]
        pub fn into_raw_wsabuf(self) -> WSABUF {
            let wsabuf = self.inner;
            core::mem::forget(self);
            wsabuf
        }

        #[inline]
        pub fn into_box(self) -> Box<[I::DerefTargetItem]> {
            let (ptr, len) = self.into_raw_parts();

            unsafe {
                Box::from_raw(core::slice::from_raw_parts_mut(
                    ptr as *mut I::DerefTargetItem,
                    len,
                ))
            }
        }
        #[inline]
        pub fn as_ioslice(&self) -> IoSlice<I> {
            IoSlice::from_inner_data(self.inner_data())
        }
        #[inline]
        pub fn as_ioslice_mut(&mut self) -> IoSliceMut<I> {
            IoSliceMut::from_inner_data(self.inner_data_mut())
        }
        #[inline]
        pub fn inner_data(&self) -> &[I::DerefTargetItem] {
            unsafe {
                core::slice::from_raw_parts(
                    self.__ptr() as *const I::DerefTargetItem,
                    self.__len(),
                )
            }
        }
        #[inline]
        pub fn inner_data_mut(&mut self) -> &mut [I::DerefTargetItem] {
            unsafe {
                core::slice::from_raw_parts_mut(
                    self.__ptr() as *mut I::DerefTargetItem,
                    self.__len()
                )
            }
        }
        #[inline]
        pub fn cast_to_ioslices(these: &[Self]) -> &[IoSlice<I>] {
            unsafe { cast_slice_same_layout(these) }
        }
        /// Cast `&mut [IoBox]` to `&mut [IoSlice]`.
        ///
        /// # Safety
        ///
        /// To avoid being able to change the pointers, which are likely going to be deallocated in
        /// this `Drop` code, unless they are changed back, this is marked as "unsafe".
        ///
        /// Refer to [`cast_to_mut_ioslices_mut`].
        ///
        /// [`cast_to_mut_ioslices_mut`]: #method.cast_to_mut_ioslices_mut
        #[inline]
        pub unsafe fn cast_to_ioslices_mut(these: &mut [Self]) -> &mut [IoSlice<I>] {
            cast_slice_same_layout_mut(these)
        }
        #[inline]
        pub fn cast_to_mut_ioslices(these: &[Self]) -> &[IoSliceMut<I>] {
            unsafe { cast_slice_same_layout(these) }
        }
        /// Cast `&mut [IoBox]` to `&mut [IoSliceMut]`.
        ///
        /// # Safety
        ///
        /// Since a mutable slice that mirrors these allows it to change the start offsets and
        /// advancing them in other ways (and even changing them to global variables etc.), this
        /// can cause the Drop code to cause UB. The caller must ensure that any pointers are
        /// changed back to what they were previously, before the drop code is run.
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
            let (ptr, len) = self.into_raw_parts();
            IoBox::from_raw_parts(ptr, len)
        }
        #[inline]
        pub fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
            unsafe { cast_slice_same_layout(self.inner_data()) }
        }
        #[inline]
        pub fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
            unsafe { cast_slice_same_layout_mut(self.inner_data_mut()) }
        }

        #[inline]
        pub fn into_uninit(self) -> IoBox<Uninitialized> {
            unsafe {
                let (ptr, len) = self.into_raw_parts();
                IoBox::from_raw_parts(ptr as *mut MaybeUninit<u8>, len)
            }
        }

        #[inline]
        pub fn into_uninit_box(self) -> Box<[MaybeUninit<u8>]> {
            self.into_uninit().into_box()
        }

        fn __ptr(&self) -> *mut I::DerefTargetItem {
            #[cfg(all(unix, feature = "libc"))]
            {
                self.inner.iov_base as *mut I::DerefTargetItem
            }
            #[cfg(all(windows, feature = "winapi"))]
            {
                self.inner.buf as *mut I::DerefTargetItem
            }
            #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
            {
                self.inner.as_ptr()
            }
        }
        #[inline]
        fn __len(&self) -> usize {
            #[cfg(all(unix, feature = "libc"))]
            {
                self.inner.iov_len as usize
            }
            #[cfg(all(windows, feature = "winapi"))]
            {
                self.inner.len as usize
            }
            #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
            {
                self.inner.len()
            }
        }
        #[inline]
        unsafe fn __construct(ptr: *mut I::DerefTargetItem, len: usize) -> Self {
            Self {
                #[cfg(all(unix, feature = "libc"))]
                inner: libc::iovec {
                    iov_base: ptr as *mut libc::c_void,
                    iov_len: len,
                },
                #[cfg(all(windows, feature = "winapi"))]
                inner: WSABUF {
                    buf: ptr as *mut CHAR,
                    len: len as ULONG,
                },
                #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
                inner: Box::from_raw(unsafe { core::slice::from_raw_parts_mut(ptr, len) }),

                _marker: PhantomData,
            }
        }
    }
    impl IoBox<Uninitialized> {
        /// Attempt to allocate `length` bytes, returning either an uninitialized heap-allocated
        /// buffer, or an error if the allocator was unable to allocate that many bytes. Note that
        /// unless called in an `#![no_std]` environment, the OS will likely give more memory than
        /// physically present, so prefer [`alloc_uninit`] instead in that case.
        ///
        /// # Panics
        ///
        /// This associated function will panic on Windows platforms when using the `winapi`
        /// feature, if the length exceeds the `WSABUF` limit of 2^32 bytes. Always check
        /// beforehand; this will never be returned as a regular allocation error.
        ///
        /// [`alloc_uninit`]: #method.alloc_uninit
        #[inline]
        pub fn try_alloc_uninit(length: usize) -> Result<IoBox<Uninitialized>, AllocationError> {
            Self::try_alloc_inner(length, false)
        }

        /// Allocate `length` uninitialized bytes.
        ///
        /// # Panics
        ///
        /// This associated function will panic if out of memory, or if the length is greater than
        /// 2^32 on Windows platforms.
        #[inline]
        pub fn alloc_uninit(length: usize) -> IoBox<Uninitialized> {
            match Self::try_alloc_uninit(length) {
                Ok(boxed) => boxed,
                Err(AllocationError(layout)) => alloc::alloc::handle_alloc_error(layout),
            }
        }

    }
    impl IoBox<Initialized> {
        #[inline]
        pub fn as_slice(&self) -> &[u8] {
            self.inner_data()
        }
        #[inline]
        pub fn as_slice_mut(&mut self) -> &mut [u8] {
            self.inner_data_mut()
        }
    }
    impl<I: Initialization> Drop for IoBox<I> {
        fn drop(&mut self) {
            #[cfg(any(all(unix, feature = "libc"), all(windows, feature = "winapi")))]
            unsafe {
                deallocate(
                    self.__ptr() as *mut u8,
                    Layout::from_size_align(
                        self.__len()
                            .checked_mul(mem::size_of::<u8>())
                            .expect("overflow on multiplication that should be a no-op"),
                        mem::align_of::<u8>(),
                    )
                    .expect("failed to deallocate due to invalid layout"),
                );
            }
        }
    }
    impl<I: Initialization> From<Box<[I::DerefTargetItem]>> for IoBox<I> {
        #[inline]
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
        #[inline]
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
        #[inline]
        fn from(vector: Vec<I::DerefTargetItem>) -> Self {
            Self::from(vector.into_boxed_slice())
        }
    }
    impl From<Vec<u8>> for IoBox<Uninitialized> {
        #[inline]
        fn from(vector: Vec<u8>) -> Self {
            Self::from(vector.into_boxed_slice())
        }
    }
    impl<I: Initialization> From<IoBox<I>> for Box<[I::DerefTargetItem]> {
        #[inline]
        fn from(io_box: IoBox<I>) -> Self {
            io_box.into_box()
        }
    }
    impl From<IoBox<Initialized>> for Box<[MaybeUninit<u8>]> {
        #[inline]
        fn from(io_box: IoBox<Initialized>) -> Self {
            io_box.into_uninit_box()
        }
    }
    impl<I: Initialization> From<IoBox<I>> for Vec<I::DerefTargetItem> {
        #[inline]
        fn from(io_box: IoBox<I>) -> Self {
            Self::from(Box::from(io_box))
        }
    }
    impl From<IoBox<Initialized>> for Vec<MaybeUninit<u8>> {
        #[inline]
        fn from(io_box: IoBox<Initialized>) -> Self {
            io_box.into_uninit_box().into()
        }
    }
    impl core::fmt::Debug for IoBox {
        #[inline]
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{:?}", self.as_slice())
        }
    }
    impl<I: Initialization> core::ops::Deref for IoBox<I> {
        type Target = [I::DerefTargetItem];

        #[inline]
        fn deref(&self) -> &Self::Target {
            self.inner_data()
        }
    }
    impl<I: Initialization> core::ops::DerefMut for IoBox<I> {
        #[inline]
        fn deref_mut(&mut self) -> &mut Self::Target {
            self.inner_data_mut()
        }
    }
    impl<I: Initialization> AsRef<[MaybeUninit<u8>]> for IoBox<I> {
        #[inline]
        fn as_ref(&self) -> &[MaybeUninit<u8>] {
            self.as_maybe_uninit_slice()
        }
    }
    impl<I: Initialization> AsMut<[MaybeUninit<u8>]> for IoBox<I> {
        #[inline]
        fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
            self.as_maybe_uninit_slice_mut()
        }
    }
    impl AsRef<[u8]> for IoBox<Initialized> {
        #[inline]
        fn as_ref(&self) -> &[u8] {
            self.as_slice()
        }
    }
    impl AsMut<[u8]> for IoBox<Initialized> {
        #[inline]
        fn as_mut(&mut self) -> &mut [u8] {
            self.as_slice_mut()
        }
    }
    impl<I: Initialization> core::borrow::Borrow<[MaybeUninit<u8>]> for IoBox<I> {
        #[inline]
        fn borrow(&self) -> &[MaybeUninit<u8>] {
            self.as_maybe_uninit_slice()
        }
    }
    impl<I: Initialization> core::borrow::BorrowMut<[MaybeUninit<u8>]> for IoBox<I> {
        #[inline]
        fn borrow_mut(&mut self) -> &mut [MaybeUninit<u8>] {
            self.as_maybe_uninit_slice_mut()
        }
    }
    impl core::borrow::Borrow<[u8]> for IoBox<Initialized> {
        #[inline]
        fn borrow(&self) -> &[u8] {
            self.as_slice()
        }
    }
    impl core::borrow::BorrowMut<[u8]> for IoBox<Initialized> {
        #[inline]
        fn borrow_mut(&mut self) -> &mut [u8] {
            self.as_slice_mut()
        }
    }
    impl PartialEq for IoBox<Initialized> {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            self.as_slice() == other.as_slice()
        }
    }
    impl PartialEq<[u8]> for IoBox<Initialized> {
        #[inline]
        fn eq(&self, other: &[u8]) -> bool {
            self.as_slice() == other
        }
    }
    impl<'a> PartialEq<IoSlice<'a, Initialized>> for IoBox<Initialized> {
        #[inline]
        fn eq(&self, other: &IoSlice<Initialized>) -> bool {
            self.as_slice() == other.as_slice()
        }
    }
    impl<'a> PartialEq<IoSliceMut<'a, Initialized>> for IoBox<Initialized> {
        #[inline]
        fn eq(&self, other: &IoSliceMut<Initialized>) -> bool {
            self.as_slice() == other.as_slice()
        }
    }
    impl Eq for IoBox<Initialized> {}
    // TODO: more impls

    unsafe impl<I: Initialization> SliceMut for IoBox<I> {
        type Initialized = IoBox<Initialized>;

        fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
            #[forbid(unconditional_recursion)]
            IoBox::as_maybe_uninit_slice(self)
        }
        fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
            #[forbid(unconditional_recursion)]
            IoBox::as_maybe_uninit_slice_mut(self)
        }

        unsafe fn assume_init(self) -> Self::Initialized {
            #[forbid(unconditional_recursion)]
            IoBox::assume_init(self)
        }
    }
}
#[cfg(feature = "alloc")]
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

    macro_rules! splitting_inner(
        ($slice:ident) => {{
            let mut buf: [u8; 13] = *b"Hello, world!";

            let full = $slice::<Initialized>::new(&mut buf);
            let (first, remainder) = full.split_at(4);
            assert_eq!(&*first, b"Hell");

            let (second, third) = remainder.split_at(5);
            assert_eq!(&*second, b"o, wo");
            assert_eq!(&*third, b"rld!");
        }}
    );
    #[test]
    fn splitting_ioslice() {
        splitting_inner!(IoSlice)
    }
    #[test]
    fn splitting_ioslice_mut() {
        splitting_inner!(IoSliceMut)
    }

    #[test]
    fn partially_init_by_copying() {
        let mut uninitialized_memory = [MaybeUninit::uninit(); 32];
        let slice = IoSliceMut::from_uninit(&mut uninitialized_memory);

        let data = *b"this is some data";
        let (initialized, remainder) = slice.partially_init_by_copying(&data);
        assert_eq!(&*initialized, data);
        assert_eq!(remainder.len(), uninitialized_memory.len() - data.len());
    }

    #[test]
    #[cfg(all(windows, feature = "winapi"))]
    #[cfg_attr(target_pointer_width = "32", ignore)]
    #[should_panic = "IoBox (or any WSABUF-based I/O slice) cannot be larger in size than ULONG, which is 32 bits on Windows."]
    fn wsabuf_limit() {
        let _ = IoBox::try_alloc_uninit(u32::MAX as usize + 1);
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
    #[test]
    fn iobox() {
        use std::io::Write;

        let iobox = IoBox::alloc_uninit(1024);
        let initialized = iobox.init_by_filling(0xFF);

        let iobox2 = IoBox::alloc_zeroed(2048);

        let boxes = [initialized, iobox2];

        let io_slices = IoSlice::cast_to_std_ioslices(IoBox::cast_to_ioslices(&boxes));

        // NOTE: This test currently depends on the fact that the Write impl for slices, never
        // only writes part of the buffers.
        let mut original_buf = [0u8; 1024 + 2048];
        let mut buf = &mut original_buf[..];
        buf.write_vectored(io_slices).unwrap();

        assert!(original_buf[..1024].iter().copied().eq(std::iter::repeat(0xFF).take(1024)));
        assert!(original_buf[1024..1024 + 2048].iter().copied().eq(std::iter::repeat(0x00).take(2048)));

        // TODO: Test more things.
    }
    // TODO: Make IoSlice compatible with WSABUF without std as well.
}

// TODO: Unfortunately &[u8] does not currently implement AsRef<[MaybeUninit<u8>]>, but in the
// future we might simply also require AsRef and AsMut.
/// A trait for mutable slices (there is not much to do at all with an uninitialized immutable
/// slice, is there?), that can be safely casted to an uninitialized slice, but also unsafely
/// assumed to be initialized when they may not be.
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
pub unsafe trait SliceMut: Sized {
    /// The type that this turns into after initialization.
    type Initialized: AsRef<[u8]> + AsMut<[u8]> + Sized;

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
    /// [`assume_init`]: #tymethod.assume_init
    fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>];

    /// Unsafely assume that the value actually is initialized, getting a value of the initialized
    /// type.
    ///
    /// # Safety
    ///
    /// The safety of calling this depends on the initialization invariant. Before this can ever be
    /// called, the caller must ensure that every byte given in [`as_maybe_uninit_slice_mut`] has
    /// been written to, or that it was already initialized.
    ///
    /// [`as_maybe_uninit_slice_mut`]: #tymethod.as_maybe_uninit_slice_mut
    unsafe fn assume_init(self) -> Self::Initialized;
}

pub unsafe trait SliceMutPartial: SliceMut {
    fn split_at(self, n: usize) -> (Self, Self);
}

pub trait SliceMutExt: private2::Sealed + SliceMut {
    #[inline]
    fn init_by_filling(mut self, byte: u8) -> Self::Initialized {
        let slice = self.as_maybe_uninit_slice_mut();

        // NOTE: This is solely to allow for any improved optimizations nightly may offer; we all
        // know that memcpy most likely is faster (and cleaner) than a loop.
        #[cfg(feature = "nightly")]
        {
            slice.fill(MaybeUninit::new(byte));
        }

        #[cfg(not(feature = "nightly"))]
        for slice_byte in slice {
            *slice_byte = MaybeUninit::new(byte);
        }

        unsafe { self.assume_init() }
    }

    #[inline]
    fn init_by_zeroing(self) -> Self::Initialized {
        self.init_by_filling(0u8)
    }

    #[inline]
    fn init_by_copying(mut self, source: &[u8]) -> Self::Initialized {
        let slice = self.as_maybe_uninit_slice_mut();
        assert_eq!(source.len(), slice.len(), "in order to fully initialize a slice-like type, the source slice must be exactly as large");
        slice.copy_from_slice(cast_init_to_uninit_slice(source));
        unsafe { self.assume_init() }
    }
}
pub trait SliceMutPartialExt: SliceMutPartial {
    #[inline]
    fn partially_init_by_filling(self, init_len: usize, byte: u8) -> (Self::Initialized, Self) {
        // NOTE: This will validate the length.
        let (mut to_initialize, residue) = self.split_at(init_len);

        to_initialize
            .as_maybe_uninit_slice_mut()
            .init_by_filling(byte);
        (unsafe { to_initialize.assume_init() }, residue)
    }
    #[inline]
    fn partially_init_by_zeroing(self, init_len: usize) -> (Self::Initialized, Self) {
        self.partially_init_by_filling(init_len, 0u8)
    }

    #[inline]
    fn partially_init_by_copying(self, source: &[u8]) -> (Self::Initialized, Self) {
        // NOTE: This will validate the length.
        let (mut to_initialize, residue) = self.split_at(source.len());

        to_initialize
            .as_maybe_uninit_slice_mut()
            .copy_from_slice(cast_init_to_uninit_slice(source));
        (unsafe { to_initialize.assume_init() }, residue)
    }
}

mod private2 {
    pub trait Sealed {}
}
mod private3 {
    pub trait Sealed {}
}

impl<T> private2::Sealed for T where T: SliceMut {}
impl<T> SliceMutExt for T where T: SliceMut {}

impl<T> private3::Sealed for T where T: SliceMutPartial {}
impl<T> SliceMutPartialExt for T where T: SliceMutPartial {}

unsafe impl<'a, I: Initialization> SliceMut for IoSliceMut<'a, I> {
    type Initialized = IoSliceMut<'a, Initialized>;

    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        #[forbid(unconditional_recursion)]
        IoSliceMut::as_maybe_uninit_slice(self)
    }
    #[inline]
    fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        #[forbid(unconditional_recursion)]
        IoSliceMut::as_maybe_uninit_slice_mut(self)
    }

    #[inline]
    unsafe fn assume_init(self) -> Self::Initialized {
        #[forbid(unconditional_recursion)]
        IoSliceMut::assume_init(self)
    }
}
// TODO: splitting for IoSliceMut

unsafe impl<'a> SliceMut for &'a mut [u8] {
    type Initialized = &'a mut [u8];

    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        cast_init_to_uninit_slice(self)
    }
    #[inline]
    fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        cast_init_to_uninit_slice_mut(self)
    }

    #[inline]
    unsafe fn assume_init(self) -> Self::Initialized {
        self
    }
}
unsafe impl<'a> SliceMut for &'a mut [MaybeUninit<u8>] {
    type Initialized = &'a mut [u8];

    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        self
    }
    #[inline]
    fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self
    }

    #[inline]
    unsafe fn assume_init(self) -> Self::Initialized {
        cast_uninit_to_init_slice_mut(self)
    }
}
unsafe impl<'a, I: Initialization> SliceMutPartial for IoSliceMut<'a, I> {
    fn split_at(self, n: usize) -> (Self, Self) {
        #[forbid(unconditional_recursion)]
        IoSliceMut::split_at(self, n)
    }
}
unsafe impl<'a> SliceMutPartial for &'a mut [u8] {
    #[inline]
    fn split_at(self, n: usize) -> (Self, Self) {
        #[forbid(unconditional_recursion)]
        <[u8]>::split_at_mut(self, n)
    }
}
unsafe impl<'a> SliceMutPartial for &'a mut [MaybeUninit<u8>] {
    #[inline]
    fn split_at(self, n: usize) -> (Self, Self) {
        #[forbid(unconditional_recursion)]
        <[MaybeUninit<u8>]>::split_at_mut(self, n)
    }
}

#[cfg(feature = "alloc")]
unsafe impl SliceMut for Box<[u8]> {
    type Initialized = Box<[u8]>;

    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        cast_init_to_uninit_slice(self)
    }
    #[inline]
    fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        cast_init_to_uninit_slice_mut(self)
    }

    #[inline]
    unsafe fn assume_init(self) -> Self::Initialized {
        self
    }
}
#[cfg(feature = "alloc")]
unsafe impl SliceMut for Box<[MaybeUninit<u8>]> {
    type Initialized = Box<[u8]>;

    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        self
    }
    #[inline]
    fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self
    }

    #[inline]
    unsafe fn assume_init(self) -> Self::Initialized {
        #[cfg(feature = "nightly")]
        {
            #[forbid(unconditional_recursion)]
            Box::assume_init(self)
        }
        #[cfg(not(feature = "nightly"))]
        {
            let slice_ptr = Box::into_raw(self);
            Box::from_raw(cast_uninit_to_init_slice_mut(&mut *slice_ptr))
        }
    }
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
/// __NOTE: This must not be used for initializing the buffer__. For that, there are are other safe
/// methods like [`SliceMutExt::init_by_filling`] and [`SliceMutExt::init_by_copying`]. If unsafe
/// code is still somehow, always initialize this by copying from _another_ MaybeUninit slice, or
/// using [`std::ptr::copy`] or [`std::ptr::copy_nonoverlapping`].
#[inline]
pub unsafe fn cast_uninit_to_init_slice_mut(uninit: &mut [MaybeUninit<u8>]) -> &mut [u8] {
    cast_slice_same_layout_mut(uninit)
}
