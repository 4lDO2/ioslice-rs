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
//! use ioslice::buffer::{Buffer, BufferRef};
//! use ioslice::traits::Initialize;
//! # // TODO: Add more safe abstractions for slices of I/O slices.
//!
//! pub trait MyRead {
//!     // NOTE: The function does not return any count, since the buffer keeps track of that.
//!     //
//!     // Rather than using `&mut Buffer<T>` directly, we use `BufferRef<'_, T>` to prevent the
//!     // caller from replacing the buffer that is being filled with something different. It also
//!     // gives the `Read` implementor a reduced subset of the functionality, to that it cannot
//!     // for example read the bytes that are already written into the buffer.
//!     fn read<'buffer, T: Initialize>(&mut self, buffer: BufferRef<'buffer, T>) -> io::Result<()>;
//! }
//!
//! impl MyRead for &[u8] {
//!     fn read<'buffer, T>(&mut self, mut buffer: BufferRef<'buffer, T>) -> io::Result<()>
//!     where
//!         T: Initialize,
//!     {
//!         // Get the minimum number of bytes to copy. Note that it will panic if the source slice
//!         // were to overflow, as with the regular `copy_from_slice` function for regular slices.
//!         let min = std::cmp::min(self.len(), buffer.remaining());
//!
//!         // Advance the buffer by simply copying the source slice.
//!         buffer.append(&self[..min]);
//!
//!         Ok(())
//!     }
//! }
//!
//! # fn main() -> io::Result<()> {
//!
//! // NOTE: The `Initialize` trait is only implemented for array sizes ranging from 0 to
//! // (including) 32, unless the `nightly` feature is enabled, which uses `min_const_generics`.
//! let array = [MaybeUninit::uninit(); 32];
//! let len = array.len();
//! let mut buf = Buffer::uninit(array);
//!
//! let original_stupid_text: &[u8] = b"copying is expensive!";
//! let mut stupid_text = original_stupid_text;
//!
//! // Read as many bytes as possible.
//! stupid_text.read(buf.by_ref())?;
//!
//! // Note that while we cannot do anything useful with the rest of the buffer, we can still use
//! // it as the destination of even more I/O, or simply check its length like we do here.
//! assert_eq!(buf.remaining(), len - original_stupid_text.len());
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
#![cfg_attr(
    feature = "nightly",
    feature(min_const_generics, new_uninit, slice_fill)
)]

#[cfg(all(unix, windows))]
compile_error!("cannot compile for both windows and unix");

pub mod buffer;
pub mod buffers;
pub mod initializer;
pub mod iovec;
pub mod traits;
pub mod wrappers;

use core::mem::MaybeUninit;

#[allow(unused_imports)]
use core::mem;

#[allow(unused_imports)]
#[cfg(feature = "alloc")]
use alloc::boxed::Box;

#[cfg(feature = "alloc")]
extern crate alloc;

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
pub fn cast_init_to_uninit_slice<U>(init: &[U]) -> &[MaybeUninit<U>] {
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
pub unsafe fn cast_uninit_to_init_slice<U>(uninit: &[MaybeUninit<U>]) -> &[U] {
    cast_slice_same_layout(uninit)
}

/// Cast a mutable slice of bytes into a slice of uninitialized bytes, pretending that it is
/// uninitialized. This is completely safe since they always have the same memory layout; however,
/// the layout of the slices themselves must not be relied upon. The initializedness information is
/// lost as part of this cast, but can be recovered when initializing again or by using unsafe
/// code.
///
/// # Safety
///
/// This is unsafe, since it allows a slice which is borrowed for a lifetime possibly shorter than
/// `'static`, to be reused after the `MaybeUninit` slice has had `MaybeUninit::uninit()` values
/// written to it. For this to be safe, the caller must only write initialized bytes to the
/// returned slice.
///
/// This function is only meant to be used in generic contexts, unlike
/// [`cast_init_to_uninit_slice`], which is used more often when copying initialized bytes to
/// uninitialized bytes.
#[inline]
pub unsafe fn cast_init_to_uninit_slice_mut<U>(init: &mut [U]) -> &mut [MaybeUninit<U>] {
    cast_slice_same_layout_mut(init)
}
/// Cast a mutable slice of possibly initialized bytes into a slice of initialized bytes, assuming
/// it is initialized.
///
/// # Safety
///
/// For this to be safe, the initialization invariant must be upheld, exactly like when reading.
///
/// __NOTE: This must not be used for initializing the buffer__. For that, there are are other safe
/// methods like [`InitializeExt::init_by_filling`] and [`InitializeExt::init_by_copying`]. If
/// unsafe code is still somehow, always initialize this by copying from _another_ MaybeUninit
/// slice, or using [`std::ptr::copy`] or [`std::ptr::copy_nonoverlapping`].
#[inline]
pub unsafe fn cast_uninit_to_init_slice_mut<U>(uninit: &mut [MaybeUninit<U>]) -> &mut [U] {
    cast_slice_same_layout_mut(uninit)
}

/// Fill a possibly uninitialized mutable slice of bytes, with the same `byte`, returning the
/// initialized slice.
#[inline]
pub fn fill_uninit_slice<U: Copy>(slice: &mut [MaybeUninit<U>], byte: U) -> &mut [U] {
    unsafe {
        // NOTE: This is solely to allow for any improved optimizations nightly may offer; we all
        // know that memset most likely is faster (and cleaner) than a loop.
        #[cfg(feature = "nightly")]
        {
            slice.fill(MaybeUninit::new(byte));
        }

        #[cfg(not(feature = "nightly"))]
        for slice_byte in slice.iter_mut() {
            *slice_byte = MaybeUninit::new(byte);
        }

        cast_uninit_to_init_slice_mut(slice)
    }
}
