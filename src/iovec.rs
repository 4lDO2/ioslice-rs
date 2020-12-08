use core::borrow::{Borrow, BorrowMut};
use core::fmt;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};

#[cfg(all(windows, feature = "winapi"))]
use winapi::shared::{
    ntdef::{CHAR, ULONG},
    ws2def::WSABUF,
};
#[cfg(feature = "redox_syscall")]
use syscall::data::IoVec;

use crate::traits::Initialize;

pub mod init_marker {
    use super::*;

    mod private {
        pub trait Sealed:
            Sized + 'static + Send + Sync + Unpin
        {
        }
    }
    pub unsafe trait InitMarker: private::Sealed {
        const IS_INITIALIZED: bool;
        type DerefTargetItem: fmt::Debug;
    }

    pub enum Init {}
    pub enum Uninit {}

    impl private::Sealed for Init {}
    impl private::Sealed for Uninit {}

    unsafe impl InitMarker for Init {
        const IS_INITIALIZED: bool = true;
        type DerefTargetItem = u8;
    }
    unsafe impl InitMarker for Uninit {
        const IS_INITIALIZED: bool = false;
        type DerefTargetItem = MaybeUninit<u8>;
    }
} // pub mod init_marker
use self::init_marker::*;

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
pub struct IoSlice<'a, I: InitMarker = Init> {
    #[cfg(all(unix, feature = "libc", not(all(feature = "redox_syscall"))))]
    inner: (libc::iovec, PhantomData<&'a [I::DerefTargetItem]>),

    #[cfg(feature = "redox_syscall")]
    inner: (IoVec, PhantomData<&'a [I::DerefTargetItem]>),

    #[cfg(all(windows, feature = "winapi"))]
    inner: (WSABUF, PhantomData<&'a [I::DerefTargetItem]>),

    #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
    inner: &'a [I::DerefTargetItem],

    _marker: PhantomData<I>,
}

// SAFETY: This is safe because whatever pointer that is sent to this slice must be Send in the
// first place. Regular slices implement Send and Sync because of this.
unsafe impl<'a, I: InitMarker> Send for IoSlice<'a, I> {}
// SAFETY: Same as above.
unsafe impl<'a, I: InitMarker> Sync for IoSlice<'a, I> {}
impl<'a, I: InitMarker> Unpin for IoSlice<'a, I> {}

#[cfg(feature = "std")]
impl<'a, I: InitMarker> std::panic::UnwindSafe for IoSlice<'a, I> {}
#[cfg(feature = "std")]
impl<'a, I: InitMarker> std::panic::RefUnwindSafe for IoSlice<'a, I> {}

impl<'a, I: InitMarker> IoSlice<'a, I> {
    /// Convert a regular slice into an I/O slice.
    ///
    /// The initializedness of the resulting I/O slice is dependent on the `I` generic parameter,
    /// which by default is [`Init`]. Note that it is highly recommended not to call this
    /// with [`Uninit`], since immutable slices cannot be made initialized, and one
    /// therefore has to prove externally that the memory is in fact initialized before using it.
    #[inline]
    pub fn new(slice: &'a [u8]) -> Self {
        unsafe { Self::__construct(slice.as_ptr(), slice.len()) }
    }

    /// Cast any I/O slice into an [`Uninit`] slice, forgetting about the original
    /// initializedness.
    #[inline]
    pub fn as_uninit(&self) -> &IoSlice<'a, Uninit> {
        unsafe { &*(self as *const Self as *const IoSlice<'a, Uninit>) }
    }
    #[inline]
    pub fn as_uninit_mut(&mut self) -> &mut IoSlice<'a, Uninit> {
        unsafe { &mut *(self as *mut Self as *mut IoSlice<'a, Uninit>) }
    }

    /// Cast any slice of I/O slice into its uninitialized counterpart.
    #[inline]
    pub fn cast_to_uninit_slices(selves: &[Self]) -> &[IoSlice<'a, Uninit>] {
        unsafe { crate::cast_slice_same_layout(selves) }
    }
    /// Cast any mutable slice of I/O slice into its uninitialized counterpart.
    #[inline]
    pub fn cast_to_uninit_slices_mut(selves: &mut [Self]) -> &mut [IoSlice<'a, Uninit>] {
        unsafe { crate::cast_slice_same_layout_mut(selves) }
    }

    /// Turn any I/O slice into an [`Uninit`] slice, forgetting about the original
    /// initializedness.
    #[inline]
    pub fn into_uninit(self) -> IoSlice<'a, Uninit> {
        unsafe { IoSlice::__construct(self.__ptr(), self.__len()) }
    }

    /// Unsafely turn an I/O slice, being already [`Init`] or not, into an I/O slice that is [`Init`].
    ///
    /// # Safety
    ///
    /// For this to be safe, the initialization invariant must be upheld. Refer to the
    /// [`std::mem::MaybeUninit`] docs.
    #[inline]
    pub unsafe fn assume_init(self) -> IoSlice<'a, Init> {
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
            #[cfg(not(feature = "redox_syscall"))]
            inner: (slice, PhantomData),

            #[cfg(feature = "redox_syscall")]
            inner: (
                IoVec {
                    addr: slice.iov_base as usize,
                    len: slice.iov_len,
                },
                PhantomData,
            ),
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
    /// aliased mutably. If the generic parameter `I` is set to `Init`, the slice must also
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
        #[cfg(not(feature = "redox_syscall"))]
        return self.inner.0;

        #[cfg(feature = "redox_syscall")]
        return libc::iovec {
            iov_base: self.inner.0.addr as *mut libc::c_void,
            iov_len: self.inner.0.len,
        };
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
        unsafe { crate::cast_slice_same_layout(slices) }
    }

    /// Cast a slice of I/O slices into a slice of `WSABUF`s. Since these must share the same ABI
    /// layout, this is completely safe, and the resulting slice can directly be passed to system
    /// calls.
    ///
    /// _This is only available on Windows targets with the `winapi` feature enabled_.
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub fn cast_to_raw_wsabufs(slices: &'a [Self]) -> &'a [WSABUF] {
        unsafe { crate::cast_slice_same_layout(slices) }
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
        crate::cast_slice_same_layout_mut(slices)
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
        unsafe {
            core::slice::from_raw_parts(self.__ptr() as *const I::DerefTargetItem, self.__len())
        }
    }
    /// Construct an I/O slice based on the inner data, which is either `[u8]` or `[MaybeUninit]`.
    #[inline]
    pub fn from_inner_data(inner_data: &'a [I::DerefTargetItem]) -> Self {
        unsafe { Self::__construct(inner_data.as_ptr() as *const u8, inner_data.len()) }
    }
    /// Retrieve a slice of possibly uninitialized data, but which is still always valid.
    #[inline]
    pub fn as_maybe_uninit_slice(&self) -> &'a [MaybeUninit<u8>] {
        self.as_uninit().inner_data()
    }
    fn __ptr(&self) -> *const u8 {
        #[cfg(all(unix, feature = "libc", not(feature = "redox_syscall")))]
        return self.inner.0.iov_base as *const u8;

        #[cfg(feature = "redox_syscall")]
        return self.inner.0.addr as *const u8;

        #[cfg(all(windows, feature = "winapi"))]
        return self.inner.0.buf as *const u8;

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        return self.inner.as_ptr() as *const u8;
    }
    fn __len(&self) -> usize {
        #[cfg(all(unix, feature = "libc", not(feature = "redox_syscall")))]
        return self.inner.0.iov_len as usize;

        #[cfg(feature = "redox_syscall")]
        return self.inner.0.len;

        #[cfg(all(windows, feature = "winapi"))]
        return self.inner.0.len as usize;

        #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
        return self.inner.len();
    }
    #[inline]
    unsafe fn __set_ptr(&mut self, ptr: *const u8) {
        #[cfg(all(unix, feature = "libc", not(feature = "redox_syscall")))]
        {
            self.inner.0.iov_base = ptr as *mut libc::c_void;
        }
        #[cfg(feature = "redox_syscall")]
        {
            self.inner.0.addr = ptr as usize;
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
        #[cfg(all(unix, feature = "libc", not(feature = "redox_syscall")))]
        {
            self.inner.0.iov_len = len as usize;
        }
        #[cfg(feature = "redox_syscall")]
        {
            self.inner.0.len = len;
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
            #[cfg(all(unix, feature = "libc", not(feature = "redox_syscall")))]
            inner: (
                libc::iovec {
                    iov_base: ptr as *mut libc::c_void,
                    iov_len: len as usize,
                },
                PhantomData,
            ),
            #[cfg(feature = "redox_syscall")]
            inner: (
                IoVec {
                    addr: ptr as usize,
                    len,
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
impl<'a> IoSlice<'a, Init> {
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
        unsafe { crate::cast_slice_same_layout(slices) }
    }
    /// Cast a mutable slice of I/O slices, into a mutable slice of libstd's [`std::io::IoSlice`].
    /// This is safe since they both must share the same ABI layout as [`libc::iovec`], and since
    /// libstd's I/O slices have the same validity invariant as this wrapper and slices in general.
    ///
    /// _This is only available with the `std` feature enabled_.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_ioslices_mut(slices: &'a mut [Self]) -> &'a mut [std::io::IoSlice<'a>] {
        unsafe { crate::cast_slice_same_layout_mut(slices) }
    }
}
impl<'a, I: InitMarker> fmt::Debug for IoSlice<'a, I> {
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
impl<'a, I: InitMarker> AsRef<[MaybeUninit<u8>]> for IoSlice<'a, I> {
    #[inline]
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        self.as_maybe_uninit_slice()
    }
}
impl<'a> AsRef<[u8]> for IoSlice<'a, Init> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}
impl<'a, I: InitMarker> Borrow<[I::DerefTargetItem]> for IoSlice<'a, I> {
    #[inline]
    fn borrow(&self) -> &[I::DerefTargetItem] {
        self.inner_data()
    }
}
impl<'a> Borrow<[MaybeUninit<u8>]> for IoSlice<'a, Init> {
    #[inline]
    fn borrow(&self) -> &[MaybeUninit<u8>] {
        self.as_maybe_uninit_slice()
    }
}
impl<'a, I: InitMarker> Deref for IoSlice<'a, I> {
    type Target = [I::DerefTargetItem];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner_data()
    }
}
impl<'a, I: InitMarker> From<&'a [I::DerefTargetItem]> for IoSlice<'a, I> {
    #[inline]
    fn from(slice: &'a [I::DerefTargetItem]) -> Self {
        Self::from_inner_data(slice)
    }
}
impl<'a, I: InitMarker> From<&'a mut [I::DerefTargetItem]> for IoSlice<'a, I> {
    #[inline]
    fn from(slice: &'a mut [I::DerefTargetItem]) -> Self {
        Self::from_inner_data(&*slice)
    }
}
impl<'a> From<&'a [u8]> for IoSlice<'a, Uninit> {
    fn from(maybe_uninit_slice: &'a [u8]) -> Self {
        Self::new(maybe_uninit_slice)
    }
}
impl<'a> From<&'a mut [u8]> for IoSlice<'a, Uninit> {
    fn from(maybe_uninit_slice: &'a mut [u8]) -> Self {
        Self::new(&*maybe_uninit_slice)
    }
}

#[cfg(feature = "nightly")]
impl<'a, I: InitMarker, const N: usize> From<&'a [I::DerefTargetItem; N]> for IoSlice<'a, I> {
    #[inline]
    fn from(array_ref: &'a [I::DerefTargetItem; N]) -> Self {
        Self::from_inner_data(&array_ref[..])
    }
}
#[cfg(feature = "nightly")]
impl<'a, I: InitMarker, const N: usize> From<&'a mut [I::DerefTargetItem; N]>
    for IoSlice<'a, I>
{
    #[inline]
    fn from(array_ref: &'a mut [I::DerefTargetItem; N]) -> Self {
        Self::from_inner_data(&array_ref[..])
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> From<&'a [u8; N]> for IoSlice<'a, Uninit> {
    #[inline]
    fn from(array_ref: &'a [u8; N]) -> Self {
        Self::new(&array_ref[..])
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> From<&'a mut [u8; N]> for IoSlice<'a, Uninit> {
    #[inline]
    fn from(array_ref: &'a mut [u8; N]) -> Self {
        Self::new(&array_ref[..])
    }
}
impl<'a> PartialEq for IoSlice<'a, Init> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self == other.as_slice()
    }
}
impl<'a> PartialEq<[u8]> for IoSlice<'a, Init> {
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialEq<[u8; N]> for IoSlice<'a, Init> {
    #[inline]
    fn eq(&self, other: &[u8; N]) -> bool {
        self == &other[..]
    }
}
impl<'a, 'b> PartialEq<IoSliceMut<'b, Init>> for IoSlice<'a, Init> {
    #[inline]
    fn eq(&self, other: &IoSliceMut<'b>) -> bool {
        self == other.as_slice()
    }
}

impl<'a> Eq for IoSlice<'a, Init> {}

impl<'a> PartialOrd<[u8]> for IoSlice<'a, Init> {
    #[inline]
    fn partial_cmp(&self, other: &[u8]) -> Option<core::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}
impl<'a, 'b> PartialOrd<IoSliceMut<'b, Init>> for IoSlice<'a, Init> {
    #[inline]
    fn partial_cmp(&self, other: &IoSliceMut<'b>) -> Option<core::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other.as_slice())
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialOrd<[u8; N]> for IoSlice<'a, Init> {
    #[inline]
    fn partial_cmp(&self, other: &[u8; N]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}

impl<'a> PartialOrd for IoSlice<'a, Init> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}
impl<'a> Ord for IoSlice<'a, Init> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        Ord::cmp(self.as_slice(), other.as_slice())
    }
}
impl<'a, I: InitMarker> Default for IoSlice<'a, I> {
    #[inline]
    fn default() -> Self {
        Self::new(&[])
    }
}
impl<'a> core::hash::Hash for IoSlice<'a, Init> {
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write(self.as_slice())
    }
}

#[cfg(feature = "std")]
impl<'a, I: InitMarker> From<std::io::IoSlice<'a>> for IoSlice<'a, I> {
    #[inline]
    fn from(slice: std::io::IoSlice<'a>) -> Self {
        unsafe { Self::__construct(slice.as_ptr(), slice.len()) }
    }
}
#[cfg(feature = "std")]
impl<'a, I: InitMarker> From<std::io::IoSliceMut<'a>> for IoSlice<'a, I> {
    #[inline]
    fn from(mut slice: std::io::IoSliceMut<'a>) -> Self {
        unsafe { Self::__construct(slice.as_mut_ptr(), slice.len()) }
    }
}
#[cfg(all(unix, feature = "libc"))]
impl<'a, I: InitMarker> From<IoSlice<'a, I>> for libc::iovec {
    #[inline]
    fn from(slice: IoSlice<'a, I>) -> Self {
        slice.as_raw_iovec()
    }
}
#[cfg(feature = "stable_deref_trait")]
unsafe impl<'a, I: InitMarker> stable_deref_trait::StableDeref for IoSlice<'a, I> {}

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
pub struct IoSliceMut<'a, I: InitMarker = Init> {
    #[cfg(all(unix, feature = "libc"))]
    inner: (libc::iovec, PhantomData<&'a mut [I::DerefTargetItem]>),

    #[cfg(all(windows, feature = "winapi"))]
    inner: (WSABUF, PhantomData<&'a mut [I::DerefTargetItem]>),

    #[cfg(not(any(all(unix, feature = "libc"), all(windows, feature = "winapi"))))]
    inner: &'a mut [I::DerefTargetItem],

    _marker: PhantomData<I>,
}
// SAFETY: Same as the safety section of impl Send for IoSlice.
unsafe impl<'a, I: InitMarker> Send for IoSliceMut<'a, I> {}
// SAFETY: Same as the safety section of impl Send for IoSlice.
unsafe impl<'a, I: InitMarker> Sync for IoSliceMut<'a, I> {}
impl<'a, I: InitMarker> Unpin for IoSliceMut<'a, I> {}

#[cfg(feature = "std")]
impl<'a, I: InitMarker> std::panic::UnwindSafe for IoSliceMut<'a, I> {}
#[cfg(feature = "std")]
impl<'a, I: InitMarker> std::panic::RefUnwindSafe for IoSliceMut<'a, I> {}

impl<'a, I: InitMarker> IoSliceMut<'a, I> {
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
    pub unsafe fn assume_init(self) -> IoSliceMut<'a, Init> {
        IoSliceMut::__construct(self.__ptr(), self.__len())
    }

    /// Unsafely cast a possibly uninitialized slice into an initialized slice, by reference.
    ///
    /// # Safety
    ///
    /// This must uphold the initialization invariant.
    #[inline]
    pub unsafe fn assume_init_ref(&self) -> &IoSliceMut<'a, Init> {
        &*(self as *const Self as *const IoSliceMut<'a, Init>)
    }
    /// Unsafely cast a possibly uninitialized slice into an initialized slice, by mutable reference.
    ///
    /// # Safety
    ///
    /// This must uphold the initialization invariant.
    #[inline]
    pub unsafe fn assume_init_mut(&mut self) -> &mut IoSliceMut<'a, Init> {
        &mut *(self as *mut Self as *mut IoSliceMut<'a, Init>)
    }

    /// Cast an I/O slice, being [`Init`] or not, into an [`Uninit`] I/O slice.
    #[inline]
    pub fn into_uninit(self) -> IoSliceMut<'a, Uninit> {
        unsafe { IoSliceMut::__construct(self.__ptr(), self.__len()) }
    }
    /// Cast an I/O slice, being [`Init`] or not, into an [`Uninit`] I/O slice, by
    /// reference.
    #[inline]
    pub fn as_uninit(&self) -> &IoSliceMut<'a, Uninit> {
        unsafe { &*(self as *const Self as *const IoSliceMut<'a, Uninit>) }
    }
    /// Cast an I/O slice, being [`Init`] or not, into an [`Uninit`] I/O slice, by
    /// mutable reference.
    #[inline]
    pub fn as_uninit_mut(&mut self) -> &mut IoSliceMut<'a, Uninit> {
        unsafe { &mut *(self as *mut Self as *mut IoSliceMut<'a, Uninit>) }
    }

    /// Cast any slice of I/O slice into its uninitialized counterpart.
    #[inline]
    pub fn cast_to_uninit_slices(selves: &[Self]) -> &[IoSliceMut<'a, Uninit>] {
        unsafe { crate::cast_slice_same_layout(selves) }
    }
    /// Cast any mutable slice of I/O slice into its uninitialized counterpart.
    ///
    /// # Safety
    ///
    /// The returned slice must not be used to de-initialize any data.
    #[inline]
    pub unsafe fn cast_to_uninit_slices_mut(
        selves: &mut [Self],
    ) -> &mut [IoSliceMut<'a, Uninit>] {
        crate::cast_slice_same_layout_mut(selves)
    }

    /// Cast any slice of I/O slice into its uninitialized counterpart.
    ///
    /// # Safety
    ///
    /// The initialization invariant must be upheld.
    #[inline]
    pub unsafe fn cast_to_init_slices(selves: &[Self]) -> &[IoSliceMut<'a, Init>] {
        crate::cast_slice_same_layout(selves)
    }
    /// Cast any mutable slice of I/O slice into its uninitialized counterpart.
    ///
    /// # Safety
    ///
    /// The initialization invariant must be upheld.
    #[inline]
    pub unsafe fn cast_to_init_slices_mut(
        selves: &mut [Self],
    ) -> &mut [IoSliceMut<'a, Init>] {
        crate::cast_slice_same_layout_mut(selves)
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
    /// Additionally, if the `I` generic parameter is [`Init`], the iovec must also point to
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
        unsafe { crate::cast_slice_same_layout(slices) }
    }
    /// Cast a slice of wrapped I/O slices into a slice of `WSABUF`s.
    #[cfg(all(windows, feature = "winapi"))]
    #[inline]
    pub fn cast_to_raw_wsabufs(slices: &[Self]) -> &[WSABUF] {
        unsafe { crate::cast_slice_same_layout(slices) }
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
        crate::cast_slice_same_layout_mut(slices)
    }
    /// Unsafely cast a mutable slice of wrapped I/O slices into a mutable slice of
    /// `WSABUF`s.
    ///
    /// # Safety
    ///
    /// This is unsafe because the initialization or validity invariants may be broken since the
    /// WSABUFs can be changed arbitrarily in a mutable reference.
    #[cfg(all(windows, feature = "winapi"))]
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
        crate::cast_slice_same_layout(slice)
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
        crate::cast_slice_same_layout_mut(slice)
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
    pub fn zeroed_by_ref<'b>(&'b mut self) -> &'b mut IoSliceMut<'a, Init> {
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
impl<'a> IoSliceMut<'a, Uninit> {
    /// Create an uninitialized mutable I/O slice from a regular uninitialized mutable byte slice.
    pub fn from_uninit(uninit: &'a mut [MaybeUninit<u8>]) -> Self {
        Self::from_inner_data(uninit)
    }
}
impl<'a> IoSliceMut<'a, Init> {
    /// Retrieve the inner slice immutably. This requires the I/O slice to be initialized.
    ///
    /// Unlike the immutable [`IoSlice`], this will require a secondary lifetime of `self`, to
    /// prevent aliasing when the data can be mutated. If it is necessary to obtain a byte slice
    /// with lifetime `'a`, use [`to_slice`].
    ///
    /// [`to_slice`]: #method.to_slice
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        unsafe { crate::cast_slice_same_layout(self.inner_data()) }
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
        unsafe { crate::cast_slice_same_layout_mut(self.inner_data_mut()) }
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
        unsafe { crate::cast_slice_same_layout(slices) }
    }

    /// Cast `&[IoSliceMut]` to `&[std::io::IoSliceMut]`.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_mut_ioslices<'b>(slices: &'b [Self]) -> &'b [std::io::IoSliceMut<'a>] {
        unsafe { crate::cast_slice_same_layout(slices) }
    }
    /// Cast `&mut [IoSliceMut]` to `&mut [std::io::IoSlice]`.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_ioslices_mut<'b>(slices: &'b mut [Self]) -> &'b mut [std::io::IoSlice<'a>] {
        unsafe { crate::cast_slice_same_layout_mut(slices) }
    }

    /// Cast `&mut [IoSliceMut]` to `&mut [std::io::IoSliceMut]`.
    #[cfg(feature = "std")]
    #[inline]
    pub fn cast_to_std_mut_ioslices_mut(
        slices: &'a mut [Self],
    ) -> &'a mut [std::io::IoSliceMut<'a>] {
        unsafe { crate::cast_slice_same_layout_mut(slices) }
    }
}

impl<'a, I: InitMarker> AsRef<[I::DerefTargetItem]> for IoSliceMut<'a, I> {
    #[inline]
    fn as_ref(&self) -> &[I::DerefTargetItem] {
        self.inner_data()
    }
}
impl<'a> AsRef<[MaybeUninit<u8>]> for IoSliceMut<'a, Init> {
    #[inline]
    fn as_ref(&self) -> &[MaybeUninit<u8>] {
        self.as_maybe_uninit_slice()
    }
}
// TODO: Use #![feature(specialization)] and make sure that there is always an AsRef and Borrow
// impl for MaybeUninit and u8 regardless of the generic parameter.
// TODO: What about #![feature(const_generics)] and use an exhaustive enum for the type markers?
impl<'a, I: InitMarker> Borrow<[MaybeUninit<u8>]> for IoSliceMut<'a, I> {
    #[inline]
    fn borrow(&self) -> &[MaybeUninit<u8>] {
        self.as_maybe_uninit_slice()
    }
}
impl<'a> Borrow<[u8]> for IoSliceMut<'a, Init> {
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}
impl<'a, I: InitMarker> Deref for IoSliceMut<'a, I> {
    type Target = [I::DerefTargetItem];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner_data()
    }
}
impl<'a> AsMut<[u8]> for IoSliceMut<'a, Init> {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_slice_mut()
    }
}
impl<'a, I: InitMarker> AsMut<[MaybeUninit<u8>]> for IoSliceMut<'a, I> {
    #[inline]
    fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_maybe_uninit_slice_mut()
    }
}
impl<'a, I: InitMarker> BorrowMut<[MaybeUninit<u8>]> for IoSliceMut<'a, I> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.as_maybe_uninit_slice_mut()
    }
}
impl<'a> BorrowMut<[u8]> for IoSliceMut<'a, Init> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [u8] {
        self.as_slice_mut()
    }
}
impl<'a, I: InitMarker> DerefMut for IoSliceMut<'a, I> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner_data_mut()
    }
}
#[cfg(all(unix, feature = "libc"))]
impl<'a, I: InitMarker> From<IoSliceMut<'a, I>> for libc::iovec {
    #[inline]
    fn from(slice: IoSliceMut<'a, I>) -> Self {
        slice.as_raw_iovec()
    }
}

impl<'a, I: InitMarker> fmt::Debug for IoSliceMut<'a, I> {
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
impl<'a> PartialEq for IoSliceMut<'a, Init> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}
impl<'a> PartialEq<[u8]> for IoSliceMut<'a, Init> {
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}
impl<'a, 'b> PartialEq<&'b [u8]> for IoSliceMut<'a, Init> {
    #[inline]
    fn eq(&self, other: &&'b [u8]) -> bool {
        self.as_slice() == *other
    }
}
impl<'a, 'b> PartialEq<IoSlice<'b, Init>> for IoSliceMut<'a, Init> {
    #[inline]
    fn eq(&self, other: &IoSlice<'b>) -> bool {
        self.as_slice() == other.as_slice()
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialEq<[u8; N]> for IoSliceMut<'a, Init> {
    #[inline]
    fn eq(&self, other: &[u8; N]) -> bool {
        self.as_slice() == &other[..]
    }
}
impl<'a> Eq for IoSliceMut<'a, Init> {}

impl<'a> PartialOrd for IoSliceMut<'a, Init> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}
impl<'a> PartialOrd<[u8]> for IoSliceMut<'a, Init> {
    #[inline]
    fn partial_cmp(&self, other: &[u8]) -> Option<core::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}
impl<'a, 'b> PartialOrd<IoSlice<'b, Init>> for IoSliceMut<'a, Init> {
    #[inline]
    fn partial_cmp(&self, other: &IoSlice<'b, Init>) -> Option<core::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other.as_slice())
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialOrd<[u8; N]> for IoSliceMut<'a, Init> {
    #[inline]
    fn partial_cmp(&self, other: &[u8; N]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}
impl<'a> Ord for IoSliceMut<'a, Init> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        Ord::cmp(self.as_slice(), other.as_slice())
    }
}
impl<'a> core::hash::Hash for IoSliceMut<'a, Init> {
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write(self.as_slice())
    }
}
impl<'a, I: InitMarker> From<&'a mut [I::DerefTargetItem]> for IoSliceMut<'a, I> {
    #[inline]
    fn from(slice: &'a mut [I::DerefTargetItem]) -> Self {
        Self::from_inner_data(slice)
    }
}
impl<'a> From<&'a mut [u8]> for IoSliceMut<'a, Uninit> {
    #[inline]
    fn from(slice: &'a mut [u8]) -> Self {
        Self::new(slice)
    }
}
#[cfg(feature = "nightly")]
impl<'a, I: InitMarker, const N: usize> From<&'a mut [I::DerefTargetItem; N]>
    for IoSliceMut<'a, I>
{
    #[inline]
    fn from(slice: &'a mut [I::DerefTargetItem; N]) -> Self {
        Self::from_inner_data(slice)
    }
}

#[cfg(feature = "stable_deref_trait")]
unsafe impl<'a> stable_deref_trait::StableDeref for IoSliceMut<'a> {}

#[cfg(feature = "nightly")]
unsafe impl<const N: usize> Initialize for [u8; N] {
    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        cast_init_to_uninit_slice(&*self)
    }
    #[inline]
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        cast_init_to_uninit_slice_mut(&mut *self)
    }
}
#[cfg(feature = "nightly")]
unsafe impl<const N: usize> Initialize for [MaybeUninit<u8>; N] {
    #[inline]
    fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
        self
    }
    #[inline]
    unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self
    }
}
#[cfg(feature = "nightly")]
impl<const N: usize> From<Init<[MaybeUninit<u8>; N]>> for [u8; N] {
    #[inline]
    fn from(init: Init<[MaybeUninit<u8>; N]>) -> [u8; N] {
        unsafe {
            // SAFETY: This is safe, since [u8; N] and [MaybeUninit<u8>; N] are guaranteed to have the
            // exact same layouts, making them interchangable except for the initialization invariant,
            // which the caller must uphold.

            // XXX: This should ideally work. See issue https://github.com/rust-lang/rust/issues/61956
            // for more information.
            //
            // core::mem::transmute::<[MaybeUninit<u8>; N], [u8; N]>(self)
            //
            // ... but, we'll have to rely on transmute_copy, which is more dangerous and requires the
            // original type to be dropped. We have no choice. Hopefully the optimizer will understand
            // this as well as it understands the regular transmute.
            //
            // XXX: Another solution would be to introduce assume_init for const-generic arrays.
            let init = core::mem::transmute_copy(&init);
            core::mem::forget(init);
            init
        }
    }
}

#[cfg(not(feature = "nightly"))]
mod for_arrays {
    use super::*;

    macro_rules! impl_initialize_for_size(
        ($size:literal) => {
            unsafe impl Initialize for [u8; $size] {
                #[inline]
                fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
                    crate::cast_init_to_uninit_slice(&*self)
                }
                #[inline]
                unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
                    crate::cast_init_to_uninit_slice_mut(&mut *self)
                }
            }
            unsafe impl Initialize for [MaybeUninit<u8>; $size] {
                #[inline]
                fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
                    &*self
                }
                #[inline]
                unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
                    &mut *self
                }
            }
            impl From<crate::wrappers::Init<[MaybeUninit<u8>; $size]>> for [u8; $size] {
                #[inline]
                fn from(init_array: crate::wrappers::Init<[MaybeUninit<u8>; $size]>) -> [u8; $size] {
                    unsafe {
                        // SAFETY: Refer to assume_init for the const generics-based version of this
                        // impl..
                        core::mem::transmute(init_array)
                    }
                }
            }
        }
    );
    macro_rules! impl_initialize_for_sizes(
        [$($size:literal),*] => {
            $(
                impl_initialize_for_size!($size);
            )*
        }
    );
    impl_initialize_for_sizes![
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30, 31, 32
    ];
}

#[cfg(feature = "alloc")]
mod io_box {
    use super::*;

    #[cfg(any(all(unix, feature = "libc"), all(windows, feature = "winapi")))]
    use alloc::alloc::dealloc as deallocate;
    use alloc::alloc::{alloc as allocate, alloc_zeroed as allocate_zeroed, Layout};

    use alloc::boxed::Box;
    use alloc::vec::Vec;

    /// An owned chunk of memory, that is ABI-compatible with [`libc::iovec`] or `WSABUF`,
    /// depending on the platform and Cargo features used.
    ///
    /// This must be allocated via the system alloc; importing pointers from _malloc(2)_ is
    /// currently not possible.
    #[repr(transparent)]
    pub struct IoBox<I: InitMarker = Init> {
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
    #[derive(Debug)]
    pub struct AllocationError(Layout);

    impl AllocationError {
        /// Retrieve the layout that the allocator failed to allocate.
        #[inline]
        pub fn layout(&self) -> &Layout {
            &self.0
        }
    }

    impl fmt::Display for AllocationError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "failed to allocate {} bytes on a {}-byte alignment for buffer",
                self.layout().size(),
                self.layout().align()
            )
        }
    }

    #[cfg(feature = "std")]
    impl std::error::Error for AllocationError {}

    impl<I: InitMarker> IoBox<I> {
        // TODO: While really niche (except maybe for O_DIRECT where buffers need to be
        // page-aligned?), one should also be able to directly specify a layout.

        fn try_alloc_inner<J: InitMarker>(
            length: usize,
            zeroed: bool,
        ) -> Result<IoBox<J>, AllocationError> {
            let layout = Layout::from_size_align(
                core::mem::size_of::<u8>()
                    .checked_mul(length)
                    .expect("overflow when multiplying length with size of u8"),
                core::mem::align_of::<u8>(),
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
                core::slice::from_raw_parts(self.__ptr() as *const I::DerefTargetItem, self.__len())
            }
        }
        #[inline]
        pub fn inner_data_mut(&mut self) -> &mut [I::DerefTargetItem] {
            unsafe {
                core::slice::from_raw_parts_mut(
                    self.__ptr() as *mut I::DerefTargetItem,
                    self.__len(),
                )
            }
        }
        #[inline]
        pub fn cast_to_ioslices(these: &[Self]) -> &[IoSlice<I>] {
            unsafe { crate::cast_slice_same_layout(these) }
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
            crate::cast_slice_same_layout_mut(these)
        }
        #[inline]
        pub fn cast_to_mut_ioslices(these: &[Self]) -> &[IoSliceMut<I>] {
            unsafe { crate::cast_slice_same_layout(these) }
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
            crate::cast_slice_same_layout_mut(these)
        }
        /// Convert `IoBox<_>` into `IoBox<Init>`, assuming that the data is initialized.
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
        pub unsafe fn assume_init(self) -> IoBox<Init> {
            let (ptr, len) = self.into_raw_parts();
            IoBox::from_raw_parts(ptr, len)
        }
        #[inline]
        pub fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
            unsafe { crate::cast_slice_same_layout(self.inner_data()) }
        }
        #[inline]
        pub fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
            unsafe { crate::cast_slice_same_layout_mut(self.inner_data_mut()) }
        }

        #[inline]
        pub fn into_uninit(self) -> IoBox<Uninit> {
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
                self.inner.as_ptr() as *mut I::DerefTargetItem
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
                inner: Box::from_raw(core::slice::from_raw_parts_mut(ptr, len)),

                _marker: PhantomData,
            }
        }
    }
    impl IoBox<Uninit> {
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
        pub fn try_alloc_uninit(length: usize) -> Result<IoBox<Uninit>, AllocationError> {
            Self::try_alloc_inner(length, false)
        }

        /// Allocate `length` uninitialized bytes.
        ///
        /// # Panics
        ///
        /// This associated function will panic if out of memory, or if the length is greater than
        /// 2^32 on Windows platforms.
        #[inline]
        pub fn alloc_uninit(length: usize) -> IoBox<Uninit> {
            match Self::try_alloc_uninit(length) {
                Ok(boxed) => boxed,
                Err(AllocationError(layout)) => alloc::alloc::handle_alloc_error(layout),
            }
        }
    }
    impl IoBox<Init> {
        #[inline]
        pub fn as_slice(&self) -> &[u8] {
            self.inner_data()
        }
        #[inline]
        pub fn as_slice_mut(&mut self) -> &mut [u8] {
            self.inner_data_mut()
        }
    }
    impl<I: InitMarker> Drop for IoBox<I> {
        fn drop(&mut self) {
            #[cfg(any(all(unix, feature = "libc"), all(windows, feature = "winapi")))]
            unsafe {
                deallocate(
                    self.__ptr() as *mut u8,
                    Layout::from_size_align(
                        self.__len()
                            .checked_mul(core::mem::size_of::<u8>())
                            .expect("overflow on multiplication that should be a no-op"),
                        core::mem::align_of::<u8>(),
                    )
                    .expect("failed to deallocate due to invalid layout"),
                );
            }
        }
    }
    impl<I: InitMarker> From<Box<[I::DerefTargetItem]>> for IoBox<I> {
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
    impl From<Box<[u8]>> for IoBox<Uninit> {
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
    impl<I: InitMarker> From<Vec<I::DerefTargetItem>> for IoBox<I> {
        #[inline]
        fn from(vector: Vec<I::DerefTargetItem>) -> Self {
            Self::from(vector.into_boxed_slice())
        }
    }
    impl From<Vec<u8>> for IoBox<Uninit> {
        #[inline]
        fn from(vector: Vec<u8>) -> Self {
            Self::from(vector.into_boxed_slice())
        }
    }
    impl<I: InitMarker> From<IoBox<I>> for Box<[I::DerefTargetItem]> {
        #[inline]
        fn from(io_box: IoBox<I>) -> Self {
            io_box.into_box()
        }
    }
    impl From<IoBox<Init>> for Box<[MaybeUninit<u8>]> {
        #[inline]
        fn from(io_box: IoBox<Init>) -> Self {
            io_box.into_uninit_box()
        }
    }
    impl<I: InitMarker> From<IoBox<I>> for Vec<I::DerefTargetItem> {
        #[inline]
        fn from(io_box: IoBox<I>) -> Self {
            Self::from(Box::from(io_box))
        }
    }
    impl From<IoBox<Init>> for Vec<MaybeUninit<u8>> {
        #[inline]
        fn from(io_box: IoBox<Init>) -> Self {
            io_box.into_uninit_box().into()
        }
    }
    impl core::fmt::Debug for IoBox {
        #[inline]
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{:?}", self.as_slice())
        }
    }
    impl<I: InitMarker> Deref for IoBox<I> {
        type Target = [I::DerefTargetItem];

        #[inline]
        fn deref(&self) -> &Self::Target {
            self.inner_data()
        }
    }
    impl<I: InitMarker> DerefMut for IoBox<I> {
        #[inline]
        fn deref_mut(&mut self) -> &mut Self::Target {
            self.inner_data_mut()
        }
    }
    impl<I: InitMarker> AsRef<[MaybeUninit<u8>]> for IoBox<I> {
        #[inline]
        fn as_ref(&self) -> &[MaybeUninit<u8>] {
            self.as_maybe_uninit_slice()
        }
    }
    impl<I: InitMarker> AsMut<[MaybeUninit<u8>]> for IoBox<I> {
        #[inline]
        fn as_mut(&mut self) -> &mut [MaybeUninit<u8>] {
            self.as_maybe_uninit_slice_mut()
        }
    }
    impl AsRef<[u8]> for IoBox<Init> {
        #[inline]
        fn as_ref(&self) -> &[u8] {
            self.as_slice()
        }
    }
    impl AsMut<[u8]> for IoBox<Init> {
        #[inline]
        fn as_mut(&mut self) -> &mut [u8] {
            self.as_slice_mut()
        }
    }
    impl<I: InitMarker> core::borrow::Borrow<[MaybeUninit<u8>]> for IoBox<I> {
        #[inline]
        fn borrow(&self) -> &[MaybeUninit<u8>] {
            self.as_maybe_uninit_slice()
        }
    }
    impl<I: InitMarker> core::borrow::BorrowMut<[MaybeUninit<u8>]> for IoBox<I> {
        #[inline]
        fn borrow_mut(&mut self) -> &mut [MaybeUninit<u8>] {
            self.as_maybe_uninit_slice_mut()
        }
    }
    impl core::borrow::Borrow<[u8]> for IoBox<Init> {
        #[inline]
        fn borrow(&self) -> &[u8] {
            self.as_slice()
        }
    }
    impl core::borrow::BorrowMut<[u8]> for IoBox<Init> {
        #[inline]
        fn borrow_mut(&mut self) -> &mut [u8] {
            self.as_slice_mut()
        }
    }
    impl PartialEq for IoBox<Init> {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            self.as_slice() == other.as_slice()
        }
    }
    impl PartialEq<[u8]> for IoBox<Init> {
        #[inline]
        fn eq(&self, other: &[u8]) -> bool {
            self.as_slice() == other
        }
    }
    impl<'a> PartialEq<IoSlice<'a, Init>> for IoBox<Init> {
        #[inline]
        fn eq(&self, other: &IoSlice<Init>) -> bool {
            self.as_slice() == other.as_slice()
        }
    }
    impl<'a> PartialEq<IoSliceMut<'a, Init>> for IoBox<Init> {
        #[inline]
        fn eq(&self, other: &IoSliceMut<Init>) -> bool {
            self.as_slice() == other.as_slice()
        }
    }
    impl Eq for IoBox<Init> {}
    // TODO: more impls

    unsafe impl<I: InitMarker> Initialize for IoBox<I> {
        fn as_maybe_uninit_slice(&self) -> &[MaybeUninit<u8>] {
            #[forbid(unconditional_recursion)]
            IoBox::as_maybe_uninit_slice(self)
        }
        unsafe fn as_maybe_uninit_slice_mut(&mut self) -> &mut [MaybeUninit<u8>] {
            #[forbid(unconditional_recursion)]
            IoBox::as_maybe_uninit_slice_mut(self)
        }
    }
    impl<I: InitMarker> From<crate::wrappers::Init<IoBox<I>>> for IoBox<init_marker::Init> {
        #[inline]
        fn from(init_iobox: crate::wrappers::Init<IoBox<I>>) -> IoBox<init_marker::Init> {
            let (ptr, len) = init_iobox.into_inner().into_raw_parts();
            let ptr = ptr as *mut u8;
            unsafe { IoBox::from_raw_parts(ptr, len) }
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

            let full = $slice::<Init>::new(&mut buf);
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
            std::mem::size_of::<IoSlice>(),
            std::mem::size_of::<std::io::IoSlice>()
        );
        assert_eq!(
            std::mem::align_of::<IoSlice>(),
            std::mem::align_of::<std::io::IoSlice>()
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
    #[cfg_attr(miri, ignore)]
    fn abi_compatibility_with_iovec() {
        use std::convert::TryInto;

        assert_eq!(std::mem::size_of::<IoSlice>(), std::mem::size_of::<libc::iovec>());
        assert_eq!(std::mem::align_of::<IoSlice>(), std::mem::align_of::<libc::iovec>());

        unsafe {
            let slice: &[u8] = b"Hello, world!";

            let iov_base = slice.as_ptr() as *mut libc::c_void;
            let iov_len = slice.len();

            let vec = libc::iovec { iov_base, iov_len };

            let wrapped: IoSlice = std::mem::transmute::<libc::iovec, IoSlice>(vec);
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
    #[cfg(feature = "std")]
    fn iobox() {
        use crate::traits::InitializeExt;
        use std::io::Write;

        let iobox = IoBox::alloc_uninit(1024);
        let initialized = iobox.init_by_filling(0xFF).into();

        let iobox2 = IoBox::alloc_zeroed(2048);

        let boxes = [initialized, iobox2];

        let io_slices = IoBox::cast_to_ioslices(&boxes);
        let io_slices = IoSlice::cast_to_std_ioslices(io_slices);

        // NOTE: This test currently depends on the fact that the Write impl for slices, never
        // only writes part of the buffers.
        let mut original_buf = [0u8; 1024 + 2048];
        let mut buf = &mut original_buf[..];
        buf.write_vectored(io_slices).unwrap();

        assert!(original_buf[..1024]
            .iter()
            .copied()
            .eq(std::iter::repeat(0xFF).take(1024)));
        assert!(original_buf[1024..1024 + 2048]
            .iter()
            .copied()
            .eq(std::iter::repeat(0x00).take(2048)));

        // TODO: Test more things.
    }
    // TODO: Make IoSlice compatible with WSABUF without std as well.
}
