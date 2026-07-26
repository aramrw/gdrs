//! codegen/intrinsics/iterators.rs
//! C ABI iterator runtime callbacks (vec_for_each, iter_for_each, iter_map, map_for_each).

unsafe extern "C" {
    fn malloc(size: usize) -> *mut std::ffi::c_void;
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_vec_for_each(vec_header_ptr: *mut u64, func_ptr: u64) {
    if vec_header_ptr.is_null() || func_ptr == 0 {
        return;
    }
    unsafe {
        let data_ptr = *vec_header_ptr as *mut u64;
        let len = *vec_header_ptr.add(1);
        if data_ptr.is_null() || len == 0 {
            return;
        }
        let f: extern "C" fn(u64) -> u64 = std::mem::transmute(func_ptr as *const ());
        for i in 0..len {
            let elem_val = *data_ptr.add(i as usize);
            f(elem_val);
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_iter_for_each(range_ptr: *mut u64, func_ptr: u64) {
    if range_ptr.is_null() || func_ptr == 0 {
        return;
    }
    unsafe {
        let start = *range_ptr;
        let end = *range_ptr.add(1);
        let f: extern "C" fn(u64) -> u64 = std::mem::transmute(func_ptr as *const ());
        for i in start..end {
            f(i);
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_iter_map(range_ptr: *mut u64, closure_ptr: u64) -> *mut u64 {
    if range_ptr.is_null() {
        return std::ptr::null_mut();
    }
    unsafe {
        let ptr = malloc(24) as *mut u64;
        *ptr = *range_ptr;
        *ptr.add(1) = *range_ptr.add(1);
        *ptr.add(2) = closure_ptr;
        ptr
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_map_for_each(map_iter_ptr: *mut u64, consumer_func_ptr: u64) {
    if map_iter_ptr.is_null() {
        return;
    }
    unsafe {
        let start = *map_iter_ptr;
        let end = *map_iter_ptr.add(1);
        let map_fn_ptr = *map_iter_ptr.add(2);
        if map_fn_ptr == 0 {
            return;
        }
        let map_fn: extern "C" fn(u64) -> u64 = std::mem::transmute(map_fn_ptr as *const ());

        if consumer_func_ptr != 0 {
            let consumer_fn: extern "C" fn(u64) -> u64 =
                std::mem::transmute(consumer_func_ptr as *const ());
            for i in start..end {
                let mapped_val = map_fn(i);
                consumer_fn(mapped_val);
            }
        } else {
            for i in start..end {
                map_fn(i);
            }
        }
    }
}
