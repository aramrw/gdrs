//! codegen/intrinsics/ffi.rs
//! C ABI FFI export functions dynamically linked by Cranelift JIT at runtime.

use std::sync::Mutex;

static JIT_ARGS: Mutex<Vec<String>> = Mutex::new(Vec::new());

pub fn set_jit_args(args: Vec<String>) {
    let mut guard = JIT_ARGS.lock().unwrap();
    *guard = args;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn gdrs_resolve_symbol(
    name_ptr: *const std::os::raw::c_char,
) -> *mut std::ffi::c_void {
    if name_ptr.is_null() {
        eprintln!("[RUNTIME ERROR] Attempted to resolve NULL symbol name");
        std::process::exit(1);
    }
    let c_str = unsafe { std::ffi::CStr::from_ptr(name_ptr) };
    let name = c_str.to_string_lossy();

    let p = unsafe { libc::dlsym(libc::RTLD_DEFAULT, name_ptr) };
    if !p.is_null() {
        return p;
    }

    let mangled = format!("_{}", name);
    if let Ok(c_mangled) = std::ffi::CString::new(mangled) {
        let p_mangled = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_mangled.as_ptr()) };
        if !p_mangled.is_null() {
            return p_mangled;
        }
    }

    eprintln!("[RUNTIME ERROR] Unable to resolve symbol: '{}'", name);
    std::process::exit(1);
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_panic(msg_ptr: *const std::os::raw::c_char) -> ! {
    let msg = if msg_ptr.is_null() {
        "explicit panic"
    } else {
        unsafe { std::ffi::CStr::from_ptr(msg_ptr).to_str().unwrap_or("explicit panic") }
    };
    eprintln!("thread 'main' panicked at '{msg}'");
    std::process::exit(101);
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_arg_count() -> i64 {
    let guard = JIT_ARGS.lock().unwrap();
    guard.len() as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_execvp(path_ptr: *const std::os::raw::c_char) -> i32 {
    if path_ptr.is_null() {
        unsafe { libc::_exit(-1) };
    }
    let argv: [*const std::os::raw::c_char; 2] = [path_ptr, std::ptr::null()];
    unsafe {
        libc::execvp(path_ptr, argv.as_ptr());
        libc::_exit(-1);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_waitpid(pid: i32) -> i32 {
    let mut status: i32 = 0;
    let res = unsafe { libc::waitpid(pid, &mut status as *mut i32, 0) };
    if res < 0 {
        return -1;
    }
    if libc::WIFEXITED(status) {
        let code = libc::WEXITSTATUS(status);
        if code == 255 {
            -1
        } else {
            code
        }
    } else {
        -1
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_arg_at(idx: i64) -> *const std::os::raw::c_char {
    let guard = JIT_ARGS.lock().unwrap();
    if idx < 0 || (idx as usize) >= guard.len() {
        return std::ptr::null();
    }
    let s = &guard[idx as usize];
    let c_str = std::ffi::CString::new(s.as_str()).unwrap();
    c_str.into_raw() as *const std::os::raw::c_char
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_args_str() -> i64 {
    let guard = JIT_ARGS.lock().unwrap();
    let joined = guard.join(" ");
    drop(guard);
    let mut bytes = joined.into_bytes();
    bytes.push(0);
    let ptr = bytes.as_ptr() as i64;
    std::mem::forget(bytes);
    ptr
}

/// Type Tag ABI:
/// 0 = Int (i64)
/// 1 = Bool (1 = true, 0 = false)
/// 2 = String (*const c_char pointer)
/// 3 = Float (f64)
#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_log(type_tag: u64, value_bits: u64) -> i64 {
    match type_tag {
        0 => println!("{}", value_bits as i64),
        1 => println!("{}", value_bits != 0),
        2 => {
            let ptr = value_bits as *const std::os::raw::c_char;
            if ptr.is_null() {
                println!("<null>");
            } else {
                let c_str = unsafe { std::ffi::CStr::from_ptr(ptr) };
                println!("{}", c_str.to_string_lossy());
            }
        }
        3 => println!("{}", f64::from_bits(value_bits)),
        _ => println!("<unknown type 0x{:x}: 0x{:x}>", type_tag, value_bits),
    }
    let _ = std::io::Write::flush(&mut std::io::stdout());
    0
}

unsafe extern "C" {
    fn malloc(size: usize) -> *mut std::ffi::c_void;
    fn realloc(ptr: *mut std::ffi::c_void, size: usize) -> *mut std::ffi::c_void;
    fn free(ptr: *mut std::ffi::c_void);
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_rc_new(val_bits: u64) -> *mut u64 {
    unsafe {
        let ptr = malloc(16) as *mut u64;
        if !ptr.is_null() {
            *ptr = 1;
            *ptr.add(1) = val_bits;
        }
        ptr
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_arc_new(val_bits: u64) -> *mut u64 {
    unsafe {
        let ptr = malloc(16) as *mut u64;
        if !ptr.is_null() {
            *ptr = 1;
            *ptr.add(1) = val_bits;
        }
        ptr
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_rc_clone(ptr: *mut u64) -> *mut u64 {
    if !ptr.is_null() {
        unsafe {
            *ptr += 1;
        }
    }
    ptr
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_arc_clone(ptr: *mut u64) -> *mut u64 {
    if !ptr.is_null() {
        let atomic_ref = unsafe { &*(ptr as *const std::sync::atomic::AtomicU64) };
        atomic_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }
    ptr
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_rc_drop(ptr: *mut u64) {
    if !ptr.is_null() {
        unsafe {
            *ptr -= 1;
            if *ptr == 0 {
                free(ptr as *mut _);
            }
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_arc_drop(ptr: *mut u64) {
    if !ptr.is_null() {
        let atomic_ref = unsafe { &*(ptr as *const std::sync::atomic::AtomicU64) };
        if atomic_ref.fetch_sub(1, std::sync::atomic::Ordering::SeqCst) == 1 {
            unsafe {
                free(ptr as *mut _);
            }
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_spawn_thread(func_ptr: u64, arg: u64) {
    if func_ptr == 0 {
        return;
    }
    std::thread::spawn(move || unsafe {
        let f: extern "C" fn(u64) -> u64 = std::mem::transmute(func_ptr as *const ());
        f(arg);
    });
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_push_str(
    header_ptr: *mut u64,
    append_str_ptr: *const std::os::raw::c_char,
) {
    if header_ptr.is_null() || append_str_ptr.is_null() {
        return;
    }
    unsafe {
        let ptr_slot = header_ptr as *mut *mut u8;
        let len_slot = header_ptr.add(1);
        let cap_slot = header_ptr.add(2);

        let append_len = std::ffi::CStr::from_ptr(append_str_ptr).to_bytes().len();
        let cur_len = if *len_slot > 0 {
            *len_slot as usize
        } else if !(*ptr_slot).is_null() {
            std::ffi::CStr::from_ptr(*ptr_slot as *const _).to_bytes().len()
        } else {
            0
        };
        let cur_cap = *cap_slot as usize;

        let needed_cap = cur_len + append_len + 1;
        if cur_cap == 0 {
            let new_cap = if needed_cap < 16 {
                16
            } else {
                needed_cap.next_power_of_two()
            };
            let new_ptr = malloc(new_cap) as *mut u8;
            if !(*ptr_slot).is_null() && cur_len > 0 {
                std::ptr::copy_nonoverlapping(*ptr_slot, new_ptr, cur_len);
            }
            std::ptr::copy_nonoverlapping(
                append_str_ptr as *const u8,
                new_ptr.add(cur_len),
                append_len,
            );
            *new_ptr.add(cur_len + append_len) = 0;
            *ptr_slot = new_ptr;
            *len_slot = (cur_len + append_len) as u64;
            *cap_slot = new_cap as u64;
        } else if needed_cap > cur_cap {
            let new_cap = needed_cap.next_power_of_two();
            let new_ptr = realloc(*ptr_slot as *mut std::ffi::c_void, new_cap) as *mut u8;
            std::ptr::copy_nonoverlapping(
                append_str_ptr as *const u8,
                new_ptr.add(cur_len),
                append_len,
            );
            *new_ptr.add(cur_len + append_len) = 0;
            *ptr_slot = new_ptr;
            *len_slot = (cur_len + append_len) as u64;
            *cap_slot = new_cap as u64;
        } else {
            std::ptr::copy_nonoverlapping(
                append_str_ptr as *const u8,
                (*ptr_slot).add(cur_len),
                append_len,
            );
            *(*ptr_slot).add(cur_len + append_len) = 0;
            *len_slot = (cur_len + append_len) as u64;
        }
    }
}

#[repr(C)]
pub struct VecHeader {
    pub data: *mut u64,
    pub len: u64,
    pub cap: u64,
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn intrinsic_vec_push(header_ptr: *mut u64, elem_val: u64) {
    if header_ptr.is_null() {
        return;
    }

    unsafe {
        let header = &mut *(header_ptr as *mut VecHeader);

        if header.len >= header.cap {
            let new_cap = if header.cap == 0 {
                8
            } else {
                header.cap.saturating_mul(2)
            };

            let new_bytes = (new_cap as usize) * std::mem::size_of::<u64>();

            let new_data = if header.cap == 0 || header.data.is_null() {
                malloc(new_bytes) as *mut u64
            } else {
                realloc(header.data as *mut std::ffi::c_void, new_bytes) as *mut u64
            };

            if new_data.is_null() {
                return;
            }

            header.data = new_data;
            header.cap = new_cap;
        }

        *header.data.add(header.len as usize) = elem_val;
        header.len += 1;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_vec_pop(header_ptr: *mut u64) -> u64 {
    if header_ptr.is_null() {
        return 0;
    }
    unsafe {
        let ptr_slot = header_ptr as *mut *mut u64;
        let len_slot = header_ptr.add(1);
        let cur_len = *len_slot as usize;

        if cur_len == 0 || (*ptr_slot).is_null() {
            return 0;
        }
        let val = *(*ptr_slot).add(cur_len - 1);
        *len_slot = (cur_len - 1) as u64;
        val
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn intrinsic_vec_new() -> *mut u64 {
    unsafe {
        let header = malloc(24) as *mut u64;
        if !header.is_null() {
            *header = std::ptr::null_mut::<u64>() as u64;
            *header.add(1) = 0;
            *header.add(2) = 0;
        }
        header
    }
}
