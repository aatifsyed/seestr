//! Pointer-wide nul-terminated strings for use in FFI.
//!
//! The following C API:
//! ```c
//! char *create(void); // may return nul
//! void destroy(char *);
//! char *get_name(struct has_name *); // may return nul
//! char *version(void); // never null
//! ```
//! Can be transcribed as follows:
//! ```
//! # use seestr::{NulTerminated, Buf};
//! # #[repr(C)]
//! # struct HasName(u8);
//! extern "C" {
//!     fn create() -> Option<Buf>;
//!     fn destroy(_: Buf);
//!     fn get_name(_: &HasName) -> Option<&NulTerminated>;
//!     fn version() -> &'static NulTerminated;
//! }
//! ```
//! As opposed to:
//! ```
//! # use core::ffi::{c_char};
//! # #[repr(C)]
//! # struct HasName(u8);
//! extern "C" {
//!     fn create() -> *mut c_char;
//!     fn destroy(_: *mut c_char);
//!     fn get_name(_: *mut HasName) -> *mut c_char;
//!     fn version() -> *mut c_char;
//! }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

use core::{
    alloc::Layout,
    borrow::{Borrow, BorrowMut},
    cmp,
    ffi::{c_char, c_void, CStr},
    fmt::{self, Write as _},
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::MaybeUninit,
    ops,
    ptr::{self, NonNull},
    slice,
};

#[cfg(feature = "alloc")]
extern crate alloc;

/// A buffer that terminates at a nul byte,
/// with a length less than [`isize::MAX`].
///
/// This type is not constructable,
/// and can only live behind a reference.
///
/// The backing buffer MUST live as long as that reference.
///
/// The buffer may be shortened by writing nul bytes into it,
/// but may never be lengthened.
///
/// A `&NulTerminated` is always a single pointer wide (unlike [`CStr`]).
#[doc(alias = "NullTerminated")]
#[repr(transparent)]
pub struct NulTerminated(
    // Use c_void so users don't get `improper_ctypes` lints.
    // Ideally this should be uninhabited.
    c_void,
);

impl NulTerminated {
    /// # Safety
    /// - `ptr` must not be null.
    /// - Invariants on [`NulTerminated`] must be upheld.
    pub const unsafe fn from_ptr<'a>(ptr: *const c_char) -> &'a Self {
        &*(ptr as *const NulTerminated)
    }
    /// The returned pointer MUST NOT outlive self.
    pub const fn as_ptr(&self) -> *const c_char {
        self as *const Self as _
    }
    /// # Safety
    /// - `ptr` must not be null.
    /// - Invariants on [`NulTerminated`] must be upheld.
    pub unsafe fn from_ptr_mut<'a>(ptr: *mut c_char) -> &'a mut Self {
        &mut *(ptr as *mut NulTerminated)
    }
    /// The returned pointer MUST NOT outlive self.
    pub fn as_ptr_mut(&mut self) -> *mut c_char {
        self as *mut Self as _
    }
    /// `true` if the buffer starts with nul.
    pub const fn is_empty(&self) -> bool {
        unsafe { *self.as_ptr() == 0 }
    }
    /// Return a shared reference to the buffer until (not including) the first nul.
    pub fn bytes(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr().cast::<u8>(), self.len()) }
    }
    /// Return a shared reference to the buffer including the first nul.
    pub fn bytes_with_nul(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr().cast::<u8>(), self.len_with_nul()) }
    }
    /// The length of the buffer until (not including) the first nul.
    pub fn len(&self) -> usize {
        #[cfg(feature = "libc")]
        unsafe {
            libc::strlen(self.as_ptr())
        }
        #[cfg(not(feature = "libc"))]
        {
            let mut ct = 0;
            let mut ptr = self.as_ptr();
            while unsafe { *ptr } != 0 {
                ct += 1;
                ptr = unsafe { ptr.add(1) }
            }
            ct
        }
    }
    /// The length of the buffer including the first nul.
    pub fn len_with_nul(&self) -> usize {
        unsafe { self.len().unchecked_add(1) }
    }
    pub const fn as_cstr(&self) -> &CStr {
        unsafe { CStr::from_ptr(self.as_ptr()) }
    }
    pub const fn from_cstr(c: &CStr) -> &Self {
        unsafe { Self::from_ptr(c.as_ptr()) }
    }
    /// Access the raw bytes until (not including) the first nul.
    ///
    /// Writing a nul in this buffer will truncate it.
    pub fn bytes_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.as_ptr_mut().cast::<u8>(), self.len()) }
    }
    /// Access the raw bytes including the first nul.
    ///
    /// # Safety
    /// - This buffer MUST contain a `nul`.
    pub unsafe fn bytes_with_nul_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.as_ptr_mut().cast::<u8>(), self.len_with_nul()) }
    }
}

impl fmt::Debug for NulTerminated {
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
impl fmt::Display for NulTerminated {
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
impl PartialEq for NulTerminated {
    fn eq(&self, other: &Self) -> bool {
        self.bytes() == other.bytes()
    }
}
impl Eq for NulTerminated {}
impl Hash for NulTerminated {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes().hash(state);
    }
}
impl Ord for NulTerminated {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.bytes().cmp(other.bytes())
    }
}
impl PartialOrd for NulTerminated {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl AsRef<[u8]> for NulTerminated {
    fn as_ref(&self) -> &[u8] {
        self.bytes()
    }
}
impl Borrow<[u8]> for NulTerminated {
    fn borrow(&self) -> &[u8] {
        self.bytes()
    }
}
impl AsMut<[u8]> for NulTerminated {
    fn as_mut(&mut self) -> &mut [u8] {
        self.bytes_mut()
    }
}
impl BorrowMut<[u8]> for NulTerminated {
    fn borrow_mut(&mut self) -> &mut [u8] {
        self.bytes_mut()
    }
}
impl ops::Deref for NulTerminated {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        self.bytes()
    }
}
impl ops::DerefMut for NulTerminated {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.bytes_mut()
    }
}

impl<'a> From<&'a NulTerminated> for &'a CStr {
    fn from(value: &'a NulTerminated) -> Self {
        value.as_cstr()
    }
}
impl<'a> From<&'a CStr> for &'a NulTerminated {
    fn from(value: &'a CStr) -> Self {
        NulTerminated::from_cstr(value)
    }
}

/// Pointer-wide,
/// owned handle to a `nul`-terminated buffer,
/// allocated with [`malloc`](libc::malloc),
/// which is [`free`](libc::free)-ed on [`Drop`].
#[cfg(feature = "libc")]
#[cfg_attr(docsrs, doc_cfg(feature = "alloc"))]
pub type Buf = BufIn<Libc>;

/// Pointer-wide,
/// owned handle to a `nul`-terminated buffer,
/// which is freed on [`Drop`].
///
/// The allocator is pluggable - see [`Allocator`].
///
/// `#[repr(transparent)]` such that `Option<Buf>` has the same layout as *mut c_char.
#[repr(transparent)]
pub struct BufIn<A: Allocator> {
    ptr: NonNull<u8>,
    alloc: PhantomData<A>,
}

impl<A: Allocator> BufIn<A> {
    /// # Safety
    /// - `ptr` must not be null.
    /// - Invariants on [`Buf`] must be upheld.
    pub unsafe fn from_ptr(ptr: *mut c_char) -> Self {
        Self {
            ptr: NonNull::new_unchecked(ptr.cast()),
            alloc: PhantomData,
        }
    }
    /// Copy `src` into the heap.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc_cfg(feature = "alloc"))]
    pub fn new(src: &CStr) -> Self {
        Self::from_bytes(src.to_bytes())
    }
    /// This will add a nul terminator.
    ///
    /// If `src` contains an interior `0`,
    /// future methods on this [`Buf`] will act truncated.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc_cfg(feature = "alloc"))]
    pub fn from_bytes(src: &[u8]) -> Self {
        match Self::try_of_bytes(src) {
            Ok(it) => it,
            Err(e) => e.handle(),
        }
    }
    /// Copies `src` to the heap, appending an nul terminator.
    ///
    /// If `src` contains an interior `0`,
    /// future methods on this [`Buf`] will act truncated.
    ///
    /// # Panics
    /// - if `src`s len is [`isize::MAX`].
    pub fn try_of_bytes(src: &[u8]) -> Result<Self, AllocError> {
        unsafe {
            Self::try_with_uninit(src.len(), |dst| {
                debug_assert_eq!(src.len(), dst.len());
                ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u8>(), dst.len());
            })
        }
    }
    /// Allocate a buffer of `len + 1`,
    /// passing a buffer of length `len` to the given function for initialization.
    ///
    /// If `f` writes (any) zeroes to the given buffer,
    /// future methods on this [`Buf`] will act truncated.
    ///
    /// # Panics
    /// - if `len` is [`isize::MAX`].
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
    /// - if `len` is [`isize::MAX`].
    pub fn try_with(len: usize, f: impl FnOnce(&mut [u8])) -> Result<Self, AllocError> {
        assert_ne!(len, isize::MAX as usize);
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
    /// - `len` must be less than [`isize::MAX`].
    pub unsafe fn try_with_uninit(
        len: usize,
        f: impl FnOnce(&mut [MaybeUninit<u8>]),
    ) -> Result<Self, AllocError> {
        let len_with_nul = len + 1;
        let ptr = A::alloc(len_with_nul)
            .ok_or(AllocError(len_with_nul))?
            .cast::<u8>();
        unsafe { ptr.add(len).write(0) }; // terminate
        let uninit =
            unsafe { slice::from_raw_parts_mut(ptr.cast::<MaybeUninit<u8>>().as_ptr(), len) };
        f(uninit);
        Ok(Self {
            ptr,
            alloc: PhantomData,
        })
    }
}

impl<A: Allocator> Drop for BufIn<A> {
    fn drop(&mut self) {
        A::free(self.ptr);
    }
}

impl<A: Allocator> ops::Deref for BufIn<A> {
    type Target = NulTerminated;
    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.cast::<NulTerminated>().as_ref() }
    }
}
impl<A: Allocator> ops::DerefMut for BufIn<A> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.ptr.cast::<NulTerminated>().as_mut() }
    }
}

impl<A: Allocator> fmt::Debug for BufIn<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        NulTerminated::fmt(self, f)
    }
}
impl<A: Allocator> fmt::Display for BufIn<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        NulTerminated::fmt(self, f)
    }
}
impl<A1: Allocator, A2: Allocator> PartialEq<BufIn<A2>> for BufIn<A1> {
    fn eq(&self, other: &BufIn<A2>) -> bool {
        NulTerminated::eq(self, other)
    }
}
impl<A: Allocator> Eq for BufIn<A> {}
impl<A: Allocator> Hash for BufIn<A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        NulTerminated::hash(self, state)
    }
}
impl<A: Allocator> Ord for BufIn<A> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        NulTerminated::cmp(self, other)
    }
}
impl<A1: Allocator, A2: Allocator> PartialOrd<BufIn<A2>> for BufIn<A1> {
    fn partial_cmp(&self, other: &BufIn<A2>) -> Option<cmp::Ordering> {
        NulTerminated::partial_cmp(self, other)
    }
}
impl<A: Allocator> AsRef<NulTerminated> for BufIn<A> {
    fn as_ref(&self) -> &NulTerminated {
        self
    }
}
impl<A: Allocator> Borrow<NulTerminated> for BufIn<A> {
    fn borrow(&self) -> &NulTerminated {
        self
    }
}
impl<A: Allocator> AsMut<NulTerminated> for BufIn<A> {
    fn as_mut(&mut self) -> &mut NulTerminated {
        self
    }
}
impl<A: Allocator> BorrowMut<NulTerminated> for BufIn<A> {
    fn borrow_mut(&mut self) -> &mut NulTerminated {
        self
    }
}
impl<A: Allocator> AsRef<[u8]> for BufIn<A> {
    fn as_ref(&self) -> &[u8] {
        NulTerminated::as_ref(self)
    }
}
impl<A: Allocator> Borrow<[u8]> for BufIn<A> {
    fn borrow(&self) -> &[u8] {
        NulTerminated::borrow(self)
    }
}
impl<A: Allocator> AsMut<[u8]> for BufIn<A> {
    fn as_mut(&mut self) -> &mut [u8] {
        NulTerminated::as_mut(self)
    }
}
impl<A: Allocator> BorrowMut<[u8]> for BufIn<A> {
    fn borrow_mut(&mut self) -> &mut [u8] {
        NulTerminated::borrow_mut(self)
    }
}

/// Returned from [`BufIn::try_of_bytes`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

/// # Safety
/// - Must act like an allocator ;)
pub unsafe trait Allocator {
    fn alloc(size: usize) -> Option<NonNull<u8>>;
    fn free(ptr: NonNull<u8>);
}

/// Use [`libc`]'s allocation functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg(feature = "libc")]
#[cfg_attr(docsrs, doc_cfg(feature = "alloc"))]
pub struct Libc;

#[cfg(feature = "libc")]
#[cfg_attr(docsrs, doc_cfg(feature = "alloc"))]
unsafe impl Allocator for Libc {
    fn alloc(size: usize) -> Option<NonNull<u8>> {
        NonNull::new(unsafe { libc::malloc(size) }.cast::<u8>())
    }
    fn free(ptr: NonNull<u8>) {
        unsafe {
            libc::free(ptr.as_ptr().cast());
        }
    }
}

#[cfg(all(test, not(feature = "libc")))]
#[test]
fn custom_strlen() {
    let s = NulTerminated::from_cstr(c"hello");
    assert_eq!(s.len(), 5);
}
