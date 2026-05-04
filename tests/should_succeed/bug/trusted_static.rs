use creusot_std::prelude::*;

#[trusted]
mod allocator {

    struct DummyAllocator;

    unsafe impl core::alloc::GlobalAlloc for DummyAllocator {
        unsafe fn alloc(&self, _layout: core::alloc::Layout) -> *mut u8 {
            panic!("no_std allocator should never be called")
        }
        unsafe fn dealloc(&self, _ptr: *mut u8, _layout: core::alloc::Layout) {
            panic!("no_std allocator should never be called")
        }
    }

    #[global_allocator]
    static ALLOCATOR: DummyAllocator = DummyAllocator;
}
