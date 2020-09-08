# ioslice-rs

Provides I/O byte slice types that implement most traits that regular slices
implement, and are ABI compatible with `struct iovec` or `WSABUF` (`WSABUF`
doesn't work in `#![no_std`).
