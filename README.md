<!-- cargo-rdme start -->

Pointer-wide nul-terminated strings for use in FFI.

The following C API:
```c
char *create(void); // may return nul
void destroy(char *);
char *get_name(struct has_name *); // may return nul
char *version(void); // never null
```
Can be transcribed as follows:
```rust
extern "C" {
    fn create() -> Option<Buf>;
    fn destroy(_: Buf);
    fn get_name(_: &HasName) -> Option<&NulTerminated>;
    fn version() -> &'static NulTerminated;
}
```
As opposed to:
```rust
extern "C" {
    fn create() -> *mut c_char;
    fn destroy(_: *mut c_char);
    fn get_name(_: *mut HasName) -> *mut c_char;
    fn version() -> *mut c_char;
}
```

<!-- cargo-rdme end -->
