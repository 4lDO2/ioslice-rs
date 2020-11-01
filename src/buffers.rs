use core::mem::MaybeUninit;

use crate::{Initialize, InitializeVectored};
use crate::initializer::BuffersInitializer;

pub struct Buffers<T> {
    initializer: BuffersInitializer<T>,
    // TODO: Use a trait to omit this field when the type already is initialized.
    // NOTE: We use this counter __only internally__. Namely, in order to avoid unnecessary bounds
    // checking when indexing buffers, this must not be changed to any arbitrary value.
    // TODO: Use some integer generic type (or perhaps simply a platform-specific type alias), to
    // reduce the memory footprint when IOV_MAX happens to be less than 65536. Or at least just
    // 32-bit.
    bytes_filled_for_vector: usize,
    // TODO: Use specialization to omit this field when there is only one buffer..
    vectors_filled: usize,
}

impl<T> Buffers<T> {
    #[inline]
    pub const fn from_initializer(initializer: BuffersInitializer<T>) -> Self {
        Self {
            initializer,
            bytes_filled_for_vector: 0,
            vectors_filled: 0,
        }
    }
    #[inline]
    pub const fn new(inner: T) -> Self {
        Self::from_initializer(BuffersInitializer::uninit(inner))
    }
    #[inline]
    pub const fn initializer(&self) -> &BuffersInitializer<T> {
        &self.initializer
    }
    #[inline]
    pub fn initializer_mut(&mut self) -> &mut BuffersInitializer<T> {
        &mut self.initializer
    }
    #[inline]
    pub fn into_initializer(self) -> BuffersInitializer<T> {
        let Self { initializer, .. } = self;

        initializer
    }
    #[inline]
    pub fn into_inner(self) -> T {
        self.into_initializer().into_inner()
    }
}
impl<T> Buffers<T>
where
    T: InitializeVectored,
{
}
