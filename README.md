# ioslice-rs
[![Build Status](https://travis-ci.org/4lDO2/ioslice-rs.svg?branch=master)](https://travis-ci.org/4lDO2/ioslice-rs)
[![Crates.io](https://img.shields.io/crates/v/ioslice.svg)](https://crates.io/crates/ioslice)
[![Documentation](https://docs.rs/ioslice/badge.svg)](https://docs.rs/ioslice/)

Provides I/O byte slice types that implement most traits that regular slices
implement, and are ABI compatible with `struct iovec` or `WSABUF` (`WSABUF`
doesn't work in `#![no_std`).
