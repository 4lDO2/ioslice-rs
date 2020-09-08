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
#![cfg_attr(feature = "nightly", feature(min_const_generics))]

use core::borrow::{Borrow, BorrowMut};
use core::{cmp, fmt, hash, ops};

#[cfg(any(feature = "std", all(unix, feature = "libc")))]
use core::mem;

/// A `#![no_std]`-friendly wrapper over the [`std::io::IoSliceMut`].
///
/// Internally, the struct will store the following based on crate features:
///
/// * `std` - wrapping [`std::io::IoSlice`] directly, with accessors for it as well as conversion
///   functions and From impls.
/// * `libc` (with `#[cfg(unix)]` - wrapping [`libc::iovec`] directly on platforms that support it,
///   together with a marker making rustc think this stores a `&'a mut [u8]`.
/// * (none) - wrapping a regular slice, that may not have the same ABI guarantees as the types
///   from std or libc have.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct IoSlice<'a> {
    #[cfg(all(unix, feature = "libc"))]
    inner: (libc::iovec, core::marker::PhantomData<&'a [u8]>),

    #[cfg(not(all(unix, feature = "libc")))]
    inner: &'a [u8],
}

// SAFETY: This is safe because whatever pointer that is sent to this slice must be Send in the
// first place. Regular slices implement Send and Sync because of this.
unsafe impl<'a> Send for IoSlice<'a> {}
// SAFETY: Same as above.
unsafe impl<'a> Sync for IoSlice<'a> {}

impl<'a> IoSlice<'a> {
    pub fn new(slice: &'a [u8]) -> Self {
        #[cfg(all(unix, feature = "libc"))]
        return Self {
            inner: (
                libc::iovec {
                    iov_base: slice.as_ptr() as *mut libc::c_void,
                    iov_len: slice.len(),
                },
                core::marker::PhantomData,
            ),
        };

        #[cfg(not(all(unix, feature = "libc")))]
        return Self { inner: slice };
    }

    pub fn as_slice(&self) -> &'a [u8] {
        #[cfg(all(unix, feature = "libc"))]
        return unsafe { core::slice::from_raw_parts(self.inner.0.iov_base as *const u8, self.inner.0.iov_len) };

        #[cfg(not(all(unix, feature = "libc")))]
        return self.inner;
    }

    #[cfg(all(unix, feature = "libc"))]
    pub unsafe fn from_raw_iovec(slice: libc::iovec) -> Self {
        Self {
            inner: (slice, core::marker::PhantomData),
        }
    }
    #[cfg(all(unix, feature = "libc"))]
    pub fn as_raw_iovec(&self) -> libc::iovec {
        libc::iovec {
            iov_base: self.as_slice().as_ptr() as *mut libc::c_void,
            iov_len: self.as_slice().len(),
        }
    }

    #[cfg(feature = "std")]
    pub fn as_std_ioslices(slices: &'a [Self]) -> &'a [std::io::IoSlice<'a>] {
        unsafe { mem::transmute(slices) }
    }
    #[cfg(feature = "std")]
    pub fn as_std_ioslices_mut(slices: &'a mut [Self]) -> &'a mut [std::io::IoSlice<'a>] {
        unsafe { mem::transmute(slices) }
    }
    #[cfg(all(unix, feature = "libc"))]
    pub fn as_raw_iovecs(slices: &'a [Self]) -> &'a [libc::iovec] {
        unsafe { mem::transmute(slices) }
    }
    #[cfg(all(unix, feature = "libc"))]
    pub unsafe fn as_raw_iovecs_mut(slices: &'a mut [Self]) -> &'a mut [libc::iovec] {
        mem::transmute(slices)
    }

    pub fn advance(&mut self, count: usize) {
        #[cfg(all(unix, feature = "libc"))]
        unsafe {
            self.inner.0.iov_len = self.inner.0.iov_len
                .checked_sub(count)
                .expect("IoSlice::advance causes length to overflow");
            self.inner.0.iov_base = self.inner.0.iov_base.add(count)
        }
        #[cfg(not(all(unix, feature = "libc")))]
        {
            self.inner = &self.inner[count..];
        }
    }
    #[must_use]
    pub fn advance_within<'b>(mut slices: &'b mut [Self], mut n: usize) -> Option<&'b mut [Self]> {
        while let Some(buffer) = slices.first_mut() {
            if n == 0 { return Some(slices) };

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
}
impl<'a> fmt::Debug for IoSlice<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt::Debug::fmt(self.as_slice(), f)
    }
}
impl<'a> AsRef<[u8]> for IoSlice<'a> {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}
impl<'a> Borrow<[u8]> for IoSlice<'a> {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}
impl<'a> ops::Deref for IoSlice<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}
impl<'a> From<&'a [u8]> for IoSlice<'a> {
    fn from(slice: &'a [u8]) -> Self {
        Self::new(slice)
    }
}
impl<'a> From<&'a mut [u8]> for IoSlice<'a> {
    fn from(slice: &'a mut [u8]) -> Self {
        Self::new(&*slice)
    }
}

#[cfg(feature = "nightly")]
impl<'a, const N: usize> From<&'a [u8; N]> for IoSlice<'a> {
    fn from(array_ref: &'a [u8; N]) -> Self {
        Self::from(&array_ref[..])
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> From<&'a mut [u8; N]> for IoSlice<'a> {
    fn from(array_ref: &'a mut [u8; N]) -> Self {
        Self::from(&array_ref[..])
    }
}
impl<'a> PartialEq for IoSlice<'a> {
    fn eq(&self, other: &Self) -> bool {
        self == other.as_slice()
    }
}
impl<'a> PartialEq<[u8]> for IoSlice<'a> {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialEq<[u8; N]> for IoSlice<'a> {
    fn eq(&self, other: &[u8; N]) -> bool {
        self == &other[..]
    }
}
impl<'a, 'b> PartialEq<IoSliceMut<'b>> for IoSlice<'a> {
    fn eq(&self, other: &IoSliceMut<'b>) -> bool {
        self == other.as_slice()
    }
}

impl<'a> Eq for IoSlice<'a> {}

impl<'a> PartialOrd<[u8]> for IoSlice<'a> {
    fn partial_cmp(&self, other: &[u8]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}
impl<'a, 'b> PartialOrd<IoSliceMut<'b>> for IoSlice<'a> {
    fn partial_cmp(&self, other: &IoSliceMut<'b>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other.as_slice())
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialOrd<[u8; N]> for IoSlice<'a> {
    fn partial_cmp(&self, other: &[u8; N]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}

impl<'a> PartialOrd for IoSlice<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}
impl<'a> Ord for IoSlice<'a> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(self.as_slice(), other.as_slice())
    }
}
impl<'a> Default for IoSlice<'a> {
    fn default() -> Self {
        Self::new(&[])
    }
}
impl<'a> hash::Hash for IoSlice<'a> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        state.write(self.as_slice())
    }
}

#[cfg(feature = "std")]
impl<'a> From<std::io::IoSlice<'a>> for IoSlice<'a> {
    fn from(slice: std::io::IoSlice<'a>) -> Self {
        Self {
            inner: (
                libc::iovec {
                    iov_base: slice.as_ptr() as *mut libc::c_void,
                    iov_len: slice.len(),
                },
                core::marker::PhantomData,
            ),
            
        }
    }
}
#[cfg(feature = "std")]
impl<'a> From<std::io::IoSliceMut<'a>> for IoSlice<'a> {
    fn from(mut slice: std::io::IoSliceMut<'a>) -> Self {
        Self {
            #[cfg(all(unix, feature = "libc"))]
            inner: (
                libc::iovec {
                    iov_base: slice.as_mut_ptr() as *mut libc::c_void,
                    iov_len: slice.len(),
                },
                core::marker::PhantomData,
            ),

            #[cfg(not(all(unix, feature = "libc")))]
            inner: unsafe { core::slice::from_raw_parts_mut(slice.as_mut_ptr(), slice.len()) }
        }
    }
}
#[cfg(all(unix, feature = "libc"))]
impl<'a> From<IoSlice<'a>> for libc::iovec {
    fn from(slice: IoSlice<'a>) -> Self {
        slice.as_raw_iovec()
    }
}

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
pub struct IoSliceMut<'a> {
    #[cfg(all(unix, feature = "libc"))]
    inner: (libc::iovec, core::marker::PhantomData<&'a mut [u8]>),

    #[cfg(not(all(unix, feature = "libc")))]
    inner: &'a mut [u8],
}
impl<'a> IoSliceMut<'a> {
    pub fn new(slice: &'a mut [u8]) -> Self {
        #[cfg(all(unix, feature = "libc"))]
        return Self {
            inner: (
                libc::iovec {
                    iov_base: slice.as_mut_ptr() as *mut libc::c_void,
                    iov_len: slice.len(),
                },
                core::marker::PhantomData,
            ),
        };

        #[cfg(not(all(unix, feature = "libc")))]
        return Self { inner: slice };
    }

    pub fn as_slice(&self) -> &[u8] {
        #[cfg(all(unix, feature = "libc"))]
        return unsafe { core::slice::from_raw_parts(self.inner.0.iov_base as *const u8, self.inner.0.iov_len) };

        #[cfg(not(all(unix, feature = "libc")))]
        return &*self.inner;
    }
    pub fn as_slice_mut<'b>(&'b mut self) -> &'b mut [u8] {
        #[cfg(all(unix, feature = "libc"))]
        return unsafe { core::slice::from_raw_parts_mut(self.inner.0.iov_base as *mut u8, self.inner.0.iov_len) };

        #[cfg(not(all(unix, feature = "libc")))]
        return self.inner;
    }


    #[cfg(all(unix, feature = "libc"))]
    pub unsafe fn from_raw_iovec(slice: libc::iovec) -> Self {
        Self {
            inner: (slice, core::marker::PhantomData),
        }
    }
    #[cfg(all(unix, feature = "libc"))]
    pub fn as_raw_iovec(&self) -> libc::iovec {
        libc::iovec {
            iov_base: self.as_slice().as_ptr() as *mut libc::c_void,
            iov_len: self.as_slice().len(),
        }
    }
    #[cfg(all(unix, feature = "libc"))]
    pub fn as_raw_iovecs(slices: &'a [Self]) -> &'a [libc::iovec] {
        unsafe { mem::transmute(slices) }
    }
    #[cfg(all(unix, feature = "libc"))]
    pub unsafe fn as_raw_iovecs_mut(slices: &'a mut [Self]) -> &'a mut [libc::iovec] {
        mem::transmute(slices)
    }

    #[cfg(all(unix, feature = "libc"))]
    pub unsafe fn slice_mut_from_raw_iovecs(slice: &mut [libc::iovec]) -> &mut [Self] {
        // SAFETY: This is safe because we can assume both that `IoSlice` from std has the exact
        // same size and alignment as `struct iovec`, as well as the raw `iovec` representation
        // itself (for the libc feature), where the marker takes up no space at all.
        mem::transmute(slice)
    }
    #[cfg(all(unix, feature = "libc"))]
    pub fn slice_mut_as_raw_iovecs(slice: &mut [Self]) -> &mut [libc::iovec] {
        // SAFETY: Like above, this is completely safe since we must assume that Self has the same
        // size and alignment and the raw iovec. Additionally, since constructing the iovec itself
        // is not unsafe, using it is.
        unsafe { mem::transmute(slice) }
    }

    #[cfg(feature = "std")]
    pub fn as_std_ioslices(slices: &'a [Self]) -> &'a [std::io::IoSlice<'a>] {
        unsafe { mem::transmute(slices) }
    }

    #[cfg(feature = "std")]
    pub fn as_std_mut_ioslices(slices: &'a [Self]) -> &'a [std::io::IoSliceMut<'a>] {
        unsafe { mem::transmute(slices) }
    }
    #[cfg(feature = "std")]
    pub fn as_std_ioslices_mut(slices: &'a mut [Self]) -> &'a mut [std::io::IoSlice<'a>] {
        unsafe { mem::transmute(slices) }
    }

    #[cfg(feature = "std")]
    pub fn as_std_mut_ioslices_mut(slices: &'a mut [Self]) -> &'a mut [std::io::IoSliceMut<'a>] {
        unsafe { mem::transmute(slices) }
    }
    pub fn advance(&mut self, count: usize) {
        #[cfg(all(unix, feature = "libc"))]
        unsafe {
            self.inner.0.iov_len = self.inner.0.iov_len
                .checked_sub(count)
                .expect("IoSlice::advance causes length to overflow");
            self.inner.0.iov_base = self.inner.0.iov_base.add(count)
        }
        #[cfg(not(all(unix, feature = "libc")))]
        unsafe {
            let new_len = self.inner.len()
                .checked_sub(count)
                .expect("IoSlice::advance causes length to overflow");
            self.inner = core::slice::from_raw_parts_mut(self.inner.as_mut_ptr().add(count), new_len);
        }
    }
    #[must_use]
    pub fn advance_within<'b>(mut slices: &'b mut [Self], mut n: usize) -> Option<&'b mut [Self]> {
        while let Some(buffer) = slices.first_mut() {
            if n == 0 { return Some(slices) };

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
}

impl<'a> AsRef<[u8]> for IoSliceMut<'a> {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}
impl<'a> Borrow<[u8]> for IoSliceMut<'a> {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}
impl<'a> ops::Deref for IoSliceMut<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}
impl<'a> AsMut<[u8]> for IoSliceMut<'a> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_slice_mut()
    }
}
impl<'a> BorrowMut<[u8]> for IoSliceMut<'a> {
    fn borrow_mut(&mut self) -> &mut [u8] {
        self.as_slice_mut()
    }
}
impl<'a> ops::DerefMut for IoSliceMut<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_slice_mut()
    }
}
#[cfg(all(unix, feature = "libc"))]
impl<'a> From<IoSliceMut<'a>> for libc::iovec {
    fn from(slice: IoSliceMut<'a>) -> Self {
        slice.as_raw_iovec()
    }
}

impl<'a> fmt::Debug for IoSliceMut<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.as_slice())
            .finish()
    }
}
impl<'a> PartialEq for IoSliceMut<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}
impl<'a> PartialEq<[u8]> for IoSliceMut<'a> {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}
impl<'a, 'b> PartialEq<IoSlice<'b>> for IoSliceMut<'a> {
    fn eq(&self, other: &IoSlice<'b>) -> bool {
        self.as_slice() == other.as_slice()
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialEq<[u8; N]> for IoSliceMut<'a> {
    fn eq(&self, other: &[u8; N]) -> bool {
        self.as_slice() == &other[..]
    }
}
impl<'a> Eq for IoSliceMut<'a> {}

impl<'a> PartialOrd for IoSliceMut<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}
impl<'a> PartialOrd<[u8]> for IoSliceMut<'a> {
    fn partial_cmp(&self, other: &[u8]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}
impl<'a, 'b> PartialOrd<IoSlice<'b>> for IoSliceMut<'a> {
    fn partial_cmp(&self, other: &IoSlice<'b>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other.as_slice())
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> PartialOrd<[u8; N]> for IoSliceMut<'a> {
    fn partial_cmp(&self, other: &[u8; N]) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_slice(), other)
    }
}
impl<'a> Ord for IoSliceMut<'a> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(self.as_slice(), other.as_slice())
    }
}
impl<'a> hash::Hash for IoSliceMut<'a> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        state.write(self.as_slice())
    }
}
impl<'a> From<&'a mut [u8]> for IoSliceMut<'a> {
    fn from(slice: &'a mut [u8]) -> Self {
        Self::new(slice)
    }
}
#[cfg(feature = "nightly")]
impl<'a, const N: usize> From<&'a mut [u8; N]> for IoSliceMut<'a> {
    fn from(slice: &'a mut [u8; N]) -> Self {
        Self::new(slice)
    }
}

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
        let mut original_ioslices = original_slices.iter().copied().map(|slice| IoSlice::from(slice)).collect::<Vec<_>>();

        let original_slices = &original_slices[..];
        let original_ioslices = &mut original_ioslices[..];

        fn check_slices(ioslices: &[IoSlice], slice: &[&[u8]]) {
            assert!(ioslices.iter().map(|ioslice| ioslice.as_slice()).eq(slice.iter().copied()));
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
        assert_eq!(mem::size_of::<IoSlice>(), mem::size_of::<std::io::IoSlice>());
        assert_eq!(mem::align_of::<IoSlice>(), mem::align_of::<std::io::IoSlice>());

        let slices = [FIRST, SECOND, THIRD, FOURTH];
        let mut ioslices = [IoSlice::new(FIRST), IoSlice::new(SECOND), IoSlice::new(THIRD), IoSlice::new(FOURTH)];
        let std_ioslices = IoSlice::as_std_ioslices(&ioslices);

        assert!(std_ioslices.iter().map(|ioslice| ioslice.as_ref()).eq(slices.iter().copied()));

        use std::io::prelude::*;

        let mut buffer = vec! [0u8; slices.iter().copied().map(<[u8]>::len).sum()].into_boxed_slice();

        let mut total = 0;

        let mut ioslices = &mut ioslices[..];

        loop {
            let std_ioslices = IoSlice::as_std_ioslices(&ioslices);

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

        let ioslices = [IoSlice::new(FIRST), IoSlice::new(SPACE), IoSlice::new(SECOND), IoSlice::new(SPACE), IoSlice::new(THIRD), IoSlice::new(FOURTH)];
        let iovecs = IoSlice::as_raw_iovecs(&ioslices);

        let mut fds = [0; 2];

        unsafe {
            libc::pipe(fds.as_mut_ptr());
        }
        let [receiver_fd, sender_fd] = fds;

        let mut buffer = vec! [0u8; ioslices.iter().map(|slice| slice.len()).sum()];
        let buffer_parts = buffer.chunks_mut(4).map(|slice| IoSliceMut::new(slice)).collect::<Vec<_>>();
        let buffer_parts_iovecs = IoSliceMut::as_raw_iovecs(&*buffer_parts);

        unsafe {
            // TODO: Maybe repeat since writev and readv don't have to return everything?
            let result = libc::writev(sender_fd, iovecs.as_ptr(), iovecs.len().try_into().unwrap());

            if result == -1 {
                panic!("failed to writev: {}", std::io::Error::last_os_error());
            }

            let result = libc::readv(receiver_fd, buffer_parts_iovecs.as_ptr(), buffer_parts_iovecs.len().try_into().unwrap());

            if result == -1 {
                panic!("failed to readv: {}", std::io::Error::last_os_error());
            }
        }
        let src_iter = ioslices.iter().flat_map(|ioslice| ioslice.as_slice()).copied();
        let dst_iter = buffer_parts.iter().flat_map(|ioslice| ioslice.as_slice()).copied();
        assert!(Iterator::eq(src_iter, dst_iter));
    }
    // TODO: Make IoSlice compatible with WSABUF without std as well.
}
