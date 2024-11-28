//! Pointer-wide nul-terminated strings for use in FFI.

#![cfg_attr(not(feature = "std"), no_std)]

use core::{
    alloc::Layout,
    borrow::{Borrow, BorrowMut},
    cmp,
    ffi::{c_char, CStr},
    fmt::{self, Write as _},
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops,
    ptr::{self, NonNull},
    slice,
};

#[cfg(feature = "alloc")]
extern crate alloc;

/// Pointer-wide, owned handle to a `nul`-terminated, [`libc::malloc`]-ed buffer.
#[repr(transparent)]
pub struct Buf {
    ptr: NonNull<u8>,
}

impl Buf {
    /// # Safety
    /// - `ptr` must not be null.
    /// - Invariants on [`Buf`] must be upheld.
    pub const unsafe fn from_ptr(ptr: *mut c_char) -> Self {
        Self {
            ptr: NonNull::new_unchecked(ptr.cast()),
        }
    }
    /// Copy `c` into the heap.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc_cfg(feature = "alloc"))]
    pub fn new(c: &CStr) -> Self {
        Self::of_bytes(c.to_bytes())
    }
    /// This will add a nul terminator.
    ///
    /// If `b` contains an interior `0`,
    /// future methods on this [`Buf`] will act truncated.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc_cfg(feature = "alloc"))]
    pub fn of_bytes(b: &[u8]) -> Self {
        match Self::try_of_bytes(b) {
            Ok(it) => it,
            Err(e) => e.handle(),
        }
    }
    /// Copies `b` to the heap, appending an nul terminator.
    ///
    /// If `b` contains an interior `0`,
    /// future methods on this [`Buf`] will act truncated.
    ///
    /// # Panics
    /// - if `b`s len is [`usize::MAX`].
    pub fn try_of_bytes(b: &[u8]) -> Result<Self, AllocError> {
        let (len, overflow) = b.len().overflowing_add(1);
        assert!(!overflow, "huge slice");
        let ptr = NonNull::new(unsafe { libc::malloc(len) })
            .ok_or(AllocError(len))?
            .cast::<u8>();
        unsafe {
            ptr.copy_from_nonoverlapping(NonNull::new_unchecked(b.as_ptr().cast_mut()), b.len());
            ptr.add(b.len()).write(0);
        };
        Ok(Self { ptr })
    }
    /// Allocate a buffer of `len + 1`,
    /// passing a buffer of length `len` to the given function for initialization.
    ///
    /// # Panics
    /// - if `len` is [`usize::MAX`].
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc_cfg(feature = "alloc"))]
    pub fn with(len: usize, f: impl FnOnce(&mut [u8])) -> Self {
        match Self::try_with(len, f) {
            Ok(it) => it,
            Err(e) => e.handle(),
        }
    }
    /// Allocate a buffer of `len + 1`,
    /// passing a buffer of length `len` to the given function for initialization.
    ///
    /// # Panics
    /// - if `len` is [`usize::MAX`].
    pub fn try_with(len: usize, f: impl FnOnce(&mut [u8])) -> Result<Self, AllocError> {
        unsafe {
            Self::try_with_uninit(len, |it| {
                let ptr = it.as_mut_ptr();
                let len = it.len();
                ptr::write_bytes(ptr, 0, len);
                f(slice::from_raw_parts_mut(ptr.cast::<u8>(), len))
            })
        }
    }
    /// Allocate a buffer of `len + 1`,
    /// passing a buffer of length `len` to the given function for initialization.
    ///
    /// # Safety
    /// - `f` must initialize the buffer it's passed.
    ///
    /// # Panics
    /// - if `len` is [`usize::MAX`].
    pub unsafe fn try_with_uninit(
        len: usize,
        f: impl FnOnce(&mut [MaybeUninit<u8>]),
    ) -> Result<Self, AllocError> {
        let (len_with_nul, overflow) = len.overflowing_add(1);
        assert!(!overflow, "huge slice");
        let ptr = NonNull::new(unsafe { libc::malloc(len_with_nul) })
            .ok_or(AllocError(len_with_nul))?
            .cast::<u8>();
        unsafe { ptr.add(len).write(0) }; // terminate
        let uninit =
            unsafe { slice::from_raw_parts_mut(ptr.cast::<MaybeUninit<u8>>().as_ptr(), len) };
        f(uninit);
        Ok(Self { ptr })
    }
}

impl Drop for Buf {
    fn drop(&mut self) {
        unsafe { libc::free(self.ptr.as_ptr().cast()) }
    }
}

impl ops::Deref for Buf {
    type Target = Mut<'static>;
    fn deref(&self) -> &Self::Target {
        unsafe { mem::transmute(self) }
    }
}
impl ops::DerefMut for Buf {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { mem::transmute(self) }
    }
}

/// Pointer-wide, non-owned, shared handle to a `nul`-terminated buffer that lives for `'a`.
///
/// Implements [`fmt::Display`].
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Ref<'a> {
    ptr: NonNull<u8>,
    life: PhantomData<&'a CStr>,
}

impl<'a> Ref<'a> {
    /// # Safety
    /// - `ptr` must not be null.
    /// - Invariants on [`Ref`] must be upheld.
    pub const unsafe fn from_ptr(ptr: *mut c_char) -> Self {
        Self {
            ptr: NonNull::new_unchecked(ptr.cast()),
            life: PhantomData,
        }
    }
    /// The buffer starts with nul.
    pub fn is_empty(&self) -> bool {
        unsafe { *self.ptr.as_ref() == 0 }
    }
    /// Return a shared reference to the buffer until (not including) the first nul.
    pub fn bytes(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len()) }
    }
    /// Return a shared reference to the buffer including the first nul.
    pub fn bytes_with_nul(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len_with_nul()) }
    }
    /// The length of the buffer until (not including) the first nul.
    pub fn len(&self) -> usize {
        unsafe { libc::strlen(self.ptr.as_ptr().cast::<c_char>()) }
    }
    /// The length of the buffer including the first nul.
    pub fn len_with_nul(&self) -> usize {
        unsafe { libc::strlen(self.ptr.as_ptr().cast::<c_char>()).unchecked_add(1) }
    }
    pub fn as_cstr(&self) -> &CStr {
        unsafe { CStr::from_bytes_with_nul_unchecked(self.bytes_with_nul()) }
    }
    pub fn from_cstr(c: &'a CStr) -> Self {
        Self {
            ptr: unsafe { NonNull::new_unchecked(c.as_ptr().cast::<u8>().cast_mut()) },
            life: PhantomData,
        }
    }
}

impl fmt::Debug for Ref<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk in self.bytes().utf8_chunks() {
            f.write_fmt(format_args!("{}", chunk.valid().escape_default()))?;
            if !chunk.invalid().is_empty() {
                f.write_char(char::REPLACEMENT_CHARACTER)?
            }
        }
        Ok(())
    }
}

impl fmt::Display for Ref<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk in self.bytes().utf8_chunks() {
            f.write_str(chunk.valid())?;
            if !chunk.invalid().is_empty() {
                f.write_char(char::REPLACEMENT_CHARACTER)?
            }
        }
        Ok(())
    }
}

impl PartialEq for Ref<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes() == other.bytes()
    }
}
impl Eq for Ref<'_> {}
impl Hash for Ref<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes().hash(state);
    }
}
impl Ord for Ref<'_> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.bytes().cmp(other.bytes())
    }
}
impl PartialOrd for Ref<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl AsRef<[u8]> for Ref<'_> {
    fn as_ref(&self) -> &[u8] {
        self.bytes()
    }
}
impl Borrow<[u8]> for Ref<'_> {
    fn borrow(&self) -> &[u8] {
        self.bytes()
    }
}

/// Pointer-wide, non-owned, exclusive handle to a `nul`-terminated buffer that lives for `'a`.
#[repr(transparent)]
pub struct Mut<'a> {
    ptr: NonNull<u8>,
    life: PhantomData<&'a CStr>,
}

impl<'a> Mut<'a> {
    /// # Safety
    /// - `ptr` must not be null.
    /// - Invariants on [`Mut`] must be upheld.
    pub const unsafe fn from_ptr(ptr: *mut c_char) -> Self {
        Self {
            ptr: NonNull::new_unchecked(ptr.cast()),
            life: PhantomData,
        }
    }
    /// Return an exclusive reference to the buffer until (not including) the first nul.
    ///
    /// Writing a nul in this buffer will truncate it.
    pub fn bytes_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len()) }
    }
    /// Return a exclusive reference to the buffer including the first nul.
    ///
    /// # Safety
    /// - This buffer MUST contain a `nul`.
    pub unsafe fn bytes_with_nul_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len_with_nul()) }
    }
}

impl<'a> ops::Deref for Mut<'a> {
    type Target = Ref<'a>;
    fn deref(&self) -> &Self::Target {
        unsafe { mem::transmute(self) }
    }
}

macro_rules! forward_traits {
    ($ty:ty) => {
        impl fmt::Debug for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <Ref as fmt::Debug>::fmt(self, f)
            }
        }
        impl fmt::Display for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <Ref as fmt::Display>::fmt(self, f)
            }
        }
        impl PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                <Ref as PartialEq>::eq(self, other)
            }
        }
        impl Eq for $ty {}
        impl Hash for $ty {
            fn hash<H: Hasher>(&self, state: &mut H) {
                <Ref as Hash>::hash(self, state)
            }
        }
        impl Ord for $ty {
            fn cmp(&self, other: &Self) -> cmp::Ordering {
                <Ref as Ord>::cmp(self, other)
            }
        }
        impl PartialOrd for $ty {
            fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
        impl AsRef<[u8]> for $ty {
            fn as_ref(&self) -> &[u8] {
                self.bytes()
            }
        }
        impl Borrow<[u8]> for $ty {
            fn borrow(&self) -> &[u8] {
                self.bytes()
            }
        }
        impl AsMut<[u8]> for $ty {
            fn as_mut(&mut self) -> &mut [u8] {
                self.bytes_mut()
            }
        }
        impl BorrowMut<[u8]> for $ty {
            fn borrow_mut(&mut self) -> &mut [u8] {
                self.bytes_mut()
            }
        }
    };
}
forward_traits!(Mut<'_>);
forward_traits!(Buf);

/// Returned from [`Buf::try_of_bytes`].
#[derive(Debug, Clone, Copy)]
pub struct AllocError(pub usize);

impl AllocError {
    pub fn into_layout(self) -> Layout {
        Layout::array::<u8>(self.0).unwrap()
    }
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc_cfg(feature = "alloc"))]
    pub fn handle(self) -> ! {
        alloc::alloc::handle_alloc_error(self.into_layout())
    }
}

impl fmt::Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("failed to allocate {} bytes", self.0))
    }
}

#[cfg(not(feature = "std"))]
impl core::error::Error for AllocError {}

#[cfg(feature = "std")]
impl std::error::Error for AllocError {}

#[cfg(feature = "std")]
impl From<AllocError> for std::io::ErrorKind {
    fn from(_: AllocError) -> Self {
        std::io::ErrorKind::OutOfMemory
    }
}
#[cfg(feature = "std")]
impl From<AllocError> for std::io::Error {
    fn from(value: AllocError) -> Self {
        std::io::Error::from(std::io::ErrorKind::from(value))
    }
}
