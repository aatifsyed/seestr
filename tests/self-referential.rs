use std::{ffi::CStr, fmt, io::Write as _, ptr};

use seestr::{Buf, NulTerminated};

#[repr(C)]
struct See {
    #[allow(dead_code)]
    buf: Buf,
    hello: *const NulTerminated,
    world: *const NulTerminated,
}

impl See {
    pub fn new(hello: &CStr, world: &CStr) -> Self {
        let hello = hello.to_bytes_with_nul();
        let world = world.to_bytes_with_nul();
        let mut hello_ptr = ptr::null::<NulTerminated>();
        let mut world_ptr = ptr::null::<NulTerminated>();
        let buf = Buf::with(hello.len() + world.len(), |mut buf| {
            hello_ptr = buf.as_ptr() as *const NulTerminated;
            buf.write_all(hello).unwrap();
            world_ptr = buf.as_ptr() as *const NulTerminated;
            buf.write_all(world).unwrap();
            assert!(buf.is_empty());
        });
        Self {
            buf,
            hello: hello_ptr,
            world: world_ptr,
        }
    }
    fn hello(&self) -> &NulTerminated {
        unsafe { &*self.hello }
    }
    fn world(&self) -> &NulTerminated {
        unsafe { &*self.world }
    }
}

impl fmt::Debug for See {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("See")
            .field("hello", self.hello())
            .field("world", self.world())
            .finish()
    }
}

#[test]
fn test() {
    dbg!(See::new(c"hello", c"world"));
}
