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
//! regardless of the features used, so long as the slice is marked as initialized.

#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(all(feature = "nightly", feature = "alloc"), feature(new_uninit))]

#[cfg(all(unix, windows))]
compile_error!("cannot compile for both windows and unix");

#[cfg(feature = "alloc")]
extern crate alloc;

mod iovec;
pub use iovec::*;

#[inline]
unsafe fn cast_slice_same_layout<A, B>(a: &[A]) -> &[B] {
    core::slice::from_raw_parts(a.as_ptr() as *const B, a.len())
}
#[inline]
unsafe fn cast_slice_same_layout_mut<A, B>(a: &mut [A]) -> &mut [B] {
    core::slice::from_raw_parts_mut(a.as_mut_ptr() as *mut B, a.len())
}
