#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>
#include <sys/wait.h>
#include <dirent.h>
#include <sys/stat.h>
#if defined(__APPLE__) || defined(__linux__)
#include <execinfo.h>
#endif

static int g_argc = 0;
static char** g_argv = NULL;

extern void gdrs_main(void);

static void gdrs_print_backtrace_or_note(void) {
    const char* bt = getenv("GDRS_BACKTRACE");
    if (bt && (strcmp(bt, "1") == 0 || strcmp(bt, "full") == 0)) {
#if defined(__APPLE__) || defined(__linux__)
        void* callstack[128];
        int frames = backtrace(callstack, 128);
        char** strs = backtrace_symbols(callstack, frames);
        if (strs) {
            fprintf(stderr, "stack backtrace:\n");
            for (int i = 0; i < frames; ++i) {
                fprintf(stderr, "  %2d: %s\n", i, strs[i]);
            }
            free(strs);
        }
#else
        fprintf(stderr, "stack backtrace: not supported on this platform\n");
#endif
    } else {
        fprintf(stderr, "note: run with `GDRS_BACKTRACE=1` environment variable to display a backtrace\n");
    }
}

void intrinsic_panic_loc(const char* msg, const char* file, int64_t line, int64_t col) {
    if (file && file[0] != '\0' && line > 0) {
        fprintf(stderr, "thread 'main' panicked at %s:%lld:%lld:\n%s\n",
                file, (long long)line, (long long)col,
                msg ? msg : "explicit panic");
    } else {
        fprintf(stderr, "thread 'main' panicked at %s\n",
                msg ? msg : "explicit panic");
    }
    gdrs_print_backtrace_or_note();
    fflush(stderr);
    exit(101);
}

void intrinsic_panic(const char* msg) {
    intrinsic_panic_loc(msg, NULL, 0, 0);
}

void intrinsic_bounds_panic_loc(int64_t idx, int64_t len, const char* file, int64_t line, int64_t col) {
    if (file && file[0] != '\0' && line > 0) {
        fprintf(stderr,
                "thread 'main' panicked at %s:%lld:%lld:\nindex out of bounds: the len is %lld but the index is %lld\n",
                file, (long long)line, (long long)col,
                (long long)len, (long long)idx);
    } else {
        fprintf(stderr,
                "thread 'main' panicked at index out of bounds: the len is %lld but the index is %lld\n",
                (long long)len, (long long)idx);
    }
    gdrs_print_backtrace_or_note();
    fflush(stderr);
    exit(101);
}

void intrinsic_bounds_panic(int64_t idx, int64_t len) {
    intrinsic_bounds_panic_loc(idx, len, NULL, 0, 0);
}

int main(int argc, char** argv) {
    setbuf(stdout, NULL);
    g_argc = argc;
    g_argv = argv;
    gdrs_main();
    return 0;
}

int64_t intrinsic_arg_count(void) {
    return (int64_t)g_argc;
}

const char* intrinsic_args_str(void) {
    if (g_argc <= 1) return "";
    size_t total = 0;
    for (int i = 1; i < g_argc; i++) total += strlen(g_argv[i]) + 1;
    char* buf = (char*)malloc(total + 1);
    if (!buf) return "";
    buf[0] = '\0';
    for (int i = 1; i < g_argc; i++) {
        if (i > 1) strcat(buf, " ");
        strcat(buf, g_argv[i]);
    }
    return buf;
}

const char* intrinsic_arg_at_str(int64_t idx) {
    if (idx < 0 || idx >= g_argc) return "";
    return g_argv[idx];
}

int64_t intrinsic_arg_at(int64_t idx) {
    if (idx < 0 || idx >= g_argc || !g_argv) return 0;
    return (int64_t)g_argv[idx];
}

static void format_float_buf(char* buf, size_t cap, double f, int is_f32) {
    if (is_f32) {
        snprintf(buf, cap, "%.7g", (float)f);
    } else {
        snprintf(buf, cap, "%.15g", f);
    }
    if (!strchr(buf, '.') && !strchr(buf, 'e') && !strchr(buf, 'E') && isfinite(f)) {
        size_t len = strlen(buf);
        if (len + 2 < cap) {
            buf[len] = '.';
            buf[len + 1] = '0';
            buf[len + 2] = '\0';
        }
    }
}

int64_t intrinsic_log_part(int64_t type_tag, int64_t value_bits, int64_t suffix) {
    if (type_tag == 0) { // Int
        printf("%lld", (long long)value_bits);
    } else if (type_tag == 1) { // Bool
        printf("%s", value_bits ? "true" : "false");
    } else if (type_tag == 2) { // Str
        const char* s = (const char*)value_bits;
        if (s) {
            printf("%s", s);
        } else {
            printf("<null>");
        }
    } else if (type_tag == 3) { // f64
        double f;
        memcpy(&f, &value_bits, sizeof(double));
        char buf[64];
        format_float_buf(buf, sizeof(buf), f, 0);
        printf("%s", buf);
    } else if (type_tag == 4) { // f32
        double f;
        memcpy(&f, &value_bits, sizeof(double));
        char buf[64];
        format_float_buf(buf, sizeof(buf), f, 1);
        printf("%s", buf);
    } else if (type_tag == 5) { // empty newline
        // prints suffix only
    } else if (type_tag == 6) { // Unsigned Int (u64, u32, u16, u8)
        printf("%llu", (unsigned long long)value_bits);
    } else {
        printf("<unknown type 0x%llx: 0x%llx>",
               (unsigned long long)type_tag,
               (unsigned long long)value_bits);
    }
    if (suffix == 1) {
        putchar(' ');
    } else if (suffix == 2) {
        putchar('\n');
        fflush(stdout);
    }
    return 0;
}

int64_t intrinsic_log(int64_t type_tag, int64_t value_bits) {
    return intrinsic_log_part(type_tag, value_bits, 2);
}

char* intrinsic_int_to_str(int64_t n) {
    char* buf = (char*)malloc(32);
    if (!buf) return NULL;
    snprintf(buf, 32, "%lld", (long long)n);
    return buf;
}

char* intrinsic_uint_to_str(uint64_t n) {
    char* buf = (char*)malloc(32);
    if (!buf) return NULL;
    snprintf(buf, 32, "%llu", (unsigned long long)n);
    return buf;
}

char* intrinsic_float_to_str(uint64_t bits) {
    double f = 0.0;
    memcpy(&f, &bits, sizeof(double));
    char* buf = (char*)malloc(64);
    if (!buf) return NULL;
    format_float_buf(buf, 64, f, 0);
    return buf;
}

char* intrinsic_f32_to_str(uint64_t bits) {
    double f = 0.0;
    memcpy(&f, &bits, sizeof(double));
    char* buf = (char*)malloc(64);
    if (!buf) return NULL;
    format_float_buf(buf, 64, f, 1);
    return buf;
}

char* intrinsic_bool_to_str(uint8_t b) {
    return strdup(b ? "true" : "false");
}

char* intrinsic_format_join(int64_t count, const char** parts, const uint8_t* is_owned) {
    size_t total = 0;
    for (int64_t i = 0; i < count; i++) {
        if (parts[i]) {
            total += strlen(parts[i]);
        }
    }
    char* buf = (char*)malloc(total + 1);
    if (!buf) return NULL;
    size_t offset = 0;
    for (int64_t i = 0; i < count; i++) {
        if (parts[i]) {
            size_t len = strlen(parts[i]);
            memcpy(buf + offset, parts[i], len);
            offset += len;
            if (is_owned && is_owned[i]) {
                free((void*)parts[i]);
            }
        }
    }
    buf[offset] = '\0';
    return buf;
}

typedef struct {
    uint64_t ptr;
    int64_t len;
    int64_t cap;
} GdrsString;

void intrinsic_format_join_to_string(int64_t count, const char** parts, const uint8_t* is_owned, GdrsString* out) {
    char* buf = intrinsic_format_join(count, parts, is_owned);
    if (!out) {
        free(buf);
        return;
    }
    if (!buf) {
        out->ptr = 0;
        out->len = 0;
        out->cap = 0;
        return;
    }
    size_t len = strlen(buf);
    out->ptr = (uint64_t)buf;
    out->len = (int64_t)len;
    out->cap = (int64_t)(len + 1);
}

void intrinsic_string_drop(GdrsString* s) {
    if (s && s->ptr && s->cap > 0) {
        free((void*)s->ptr);
        s->ptr = 0;
        s->len = 0;
        s->cap = 0;
    }
}

int8_t intrinsic_str_eq(int64_t a, int64_t a_is_obj, int64_t b, int64_t b_is_obj) {
    const char* sa = a_is_obj
        ? (a ? (((const char**)a)[0] ? ((const char**)a)[0] : "") : "")
        : (a ? (const char*)a : "");
    const char* sb = b_is_obj
        ? (b ? (((const char**)b)[0] ? ((const char**)b)[0] : "") : "")
        : (b ? (const char*)b : "");
    return strcmp(sa, sb) == 0 ? 1 : 0;
}

// Process intrinsics
int32_t intrinsic_execvp(const char* path_ptr) {
    if (!path_ptr) {
        _exit(-1);
    }
    char* const argv[] = { (char*)path_ptr, NULL };
    execvp(path_ptr, argv);
    _exit(-1);
    return -1;
}

int32_t intrinsic_waitpid(int32_t pid) {
    int status = 0;
    pid_t res = waitpid((pid_t)pid, &status, 0);
    if (res < 0) {
        return -1;
    }
    if (WIFEXITED(status)) {
        int code = WEXITSTATUS(status);
        return (code == 255) ? -1 : code;
    }
    return -1;
}

// Math FFI wrappers (corresponding to std/math.gdrs extern "C")
double c_exp(double x) { return exp(x); }
double c_sqrt(double x) { return sqrt(x); }
double c_sin(double x) { return sin(x); }
double c_cos(double x) { return cos(x); }
double c_tan(double x) { return tan(x); }
double c_pow(double base, double ex) { return pow(base, ex); }
double c_fabs(double x) { return fabs(x); }

// Thread Spawning
typedef struct {
    void (*func)(int64_t);
    int64_t arg;
} ThreadArgs;

static void* thread_entry(void* p) {
    ThreadArgs* args = (ThreadArgs*)p;
    if (args && args->func) {
        args->func(args->arg);
    }
    free(args);
    return NULL;
}

int64_t intrinsic_spawn_thread(int64_t func_ptr, int64_t arg) {
    if (func_ptr == 0) return 0;
    ThreadArgs* targs = (ThreadArgs*)malloc(sizeof(ThreadArgs));
    if (!targs) return 0;
    targs->func = (void (*)(int64_t))func_ptr;
    targs->arg = arg;

    pthread_t thread;
    if (pthread_create(&thread, NULL, thread_entry, targs) != 0) {
        free(targs);
        return -1;
    }
    pthread_detach(thread);
    return 0;
}

// Smart Pointer rc[T] (Reference Counted: { ref_count, payload, dtor })
int64_t intrinsic_rc_new(int64_t val, int64_t dtor_fn) {
    uint64_t* ptr = (uint64_t*)malloc(24);
    if (!ptr) return 0;
    ptr[0] = 1; // ref_count
    ptr[1] = (uint64_t)val; // payload
    ptr[2] = (uint64_t)dtor_fn; // inner drop function pointer (or 0)
    return (int64_t)ptr;
}

int64_t intrinsic_rc_clone(int64_t ptr_val) {
    if (ptr_val == 0) return 0;
    uint64_t* ptr = (uint64_t*)ptr_val;
    ptr[0] += 1;
    return ptr_val;
}

int64_t intrinsic_rc_drop(int64_t ptr_val) {
    if (ptr_val == 0) return 0;
    uint64_t* ptr = (uint64_t*)ptr_val;
    if (ptr[0] > 0) {
        ptr[0] -= 1;
        if (ptr[0] == 0) {
            if (ptr[2] != 0) {
                void (*dtor)(int64_t) = (void (*)(int64_t))ptr[2];
                dtor((int64_t)ptr[1]);
            }
            free(ptr);
        }
    }
    return 0;
}

// Smart Pointer arc[T] (Atomic Reference Counted: { ref_count, payload, dtor })
int64_t intrinsic_arc_new(int64_t val, int64_t dtor_fn) {
    _Atomic uint64_t* ptr = (_Atomic uint64_t*)malloc(24);
    if (!ptr) return 0;
    atomic_init(&ptr[0], 1);
    ((uint64_t*)ptr)[1] = (uint64_t)val;
    ((uint64_t*)ptr)[2] = (uint64_t)dtor_fn;
    return (int64_t)ptr;
}

int64_t intrinsic_arc_clone(int64_t ptr_val) {
    if (ptr_val == 0) return 0;
    _Atomic uint64_t* ptr = (_Atomic uint64_t*)ptr_val;
    atomic_fetch_add(&ptr[0], 1);
    return ptr_val;
}

int64_t intrinsic_arc_drop(int64_t ptr_val) {
    if (ptr_val == 0) return 0;
    _Atomic uint64_t* ptr = (_Atomic uint64_t*)ptr_val;
    if (atomic_fetch_sub(&ptr[0], 1) == 1) {
        uint64_t* raw = (uint64_t*)ptr;
        if (raw[2] != 0) {
            void (*dtor)(int64_t) = (void (*)(int64_t))raw[2];
            dtor((int64_t)raw[1]);
        }
        free(ptr);
    }
    return 0;
}

// Vector Intrinsics
uint64_t* intrinsic_vec_new(void) {
    uint64_t* header = (uint64_t*)malloc(24);
    if (header) {
        header[0] = 0; // data
        header[1] = 0; // len
        header[2] = 0; // cap
    }
    return header;
}

int64_t intrinsic_vec_push(int64_t vec_ptr_val, int64_t val) {
    if (vec_ptr_val == 0) return 0;
    uint64_t* vec = (uint64_t*)vec_ptr_val;
    uint64_t len = vec[1];
    uint64_t cap = vec[2];
    uint64_t* buf = (uint64_t*)vec[0];

    if (len >= cap) {
        uint64_t new_cap = cap == 0 ? 8 : cap * 2;
        uint64_t* new_buf = (cap == 0 || buf == NULL)
            ? (uint64_t*)malloc(new_cap * sizeof(uint64_t))
            : (uint64_t*)realloc(buf, new_cap * sizeof(uint64_t));
        if (!new_buf) return 0;
        buf = new_buf;
        vec[0] = (uint64_t)buf;
        vec[2] = new_cap;
    }
    buf[len] = (uint64_t)val;
    vec[1] = len + 1;
    return 0;
}

int64_t intrinsic_vec_pop(int64_t vec_ptr_val) {
    if (vec_ptr_val == 0) return 0;
    uint64_t* vec = (uint64_t*)vec_ptr_val;
    uint64_t len = vec[1];
    if (len == 0) return 0;
    uint64_t* buf = (uint64_t*)vec[0];
    if (!buf) return 0;
    vec[1] = len - 1;
    return (int64_t)buf[len - 1];
}

// String Concatenation (safe even when cap == 0 and buf points to .rodata literal)
int64_t intrinsic_push_str(int64_t header_ptr_val, const char* str) {
    if (header_ptr_val == 0 || !str) return 0;
    uint64_t* header = (uint64_t*)header_ptr_val;
    char* buf = (char*)header[0];
    uint64_t cur_cap = header[2];
    uint64_t cur_len = header[1];
    if (cur_len == 0 && buf != NULL) {
        cur_len = strlen(buf);
    }

    size_t append_len = strlen(str);
    size_t needed_cap = (size_t)cur_len + append_len + 1;

    if (cur_cap == 0) {
        size_t new_cap = 16;
        while (new_cap < needed_cap) new_cap *= 2;
        char* new_buf = (char*)malloc(new_cap);
        if (!new_buf) return 0;
        if (buf != NULL && cur_len > 0) {
            memcpy(new_buf, buf, cur_len);
        }
        memcpy(new_buf + cur_len, str, append_len);
        new_buf[cur_len + append_len] = '\0';
        header[0] = (uint64_t)new_buf;
        header[1] = cur_len + append_len;
        header[2] = new_cap;
    } else if (needed_cap > cur_cap) {
        size_t new_cap = cur_cap;
        while (new_cap < needed_cap) new_cap *= 2;
        char* new_buf = (char*)realloc(buf, new_cap);
        if (!new_buf) return 0;
        memcpy(new_buf + cur_len, str, append_len);
        new_buf[cur_len + append_len] = '\0';
        header[0] = (uint64_t)new_buf;
        header[1] = cur_len + append_len;
        header[2] = new_cap;
    } else {
        memcpy(buf + cur_len, str, append_len);
        buf[cur_len + append_len] = '\0';
        header[1] = cur_len + append_len;
    }
    return 0;
}

// Filesystem directory reading intrinsic (populates caller's stack Vec<DirEntry>)
typedef struct {
    uint64_t ptr;
    int64_t len;
    int64_t cap;
} GdrsVec;

typedef struct {
    GdrsString path_str;
    GdrsString name_str;
    uint8_t is_directory;
    uint8_t is_regular_file;
    uint8_t _pad[6];
} GdrsDirEntry;

static GdrsString make_gdrs_string(const char* s) {
    size_t len = s ? strlen(s) : 0;
    char* copy = s ? strdup(s) : strdup("");
    GdrsString out;
    out.ptr = (uint64_t)copy;
    out.len = (int64_t)len;
    out.cap = (int64_t)(len + 1);
    return out;
}

int64_t gdrs_fs_read_dir(const char* path_ptr, void* out_vec_ptr) {
    if (!path_ptr || !out_vec_ptr) return -1;
    DIR* dir = opendir(path_ptr);
    if (!dir) return -1;

    GdrsVec* vec = (GdrsVec*)out_vec_ptr;
    GdrsDirEntry* buf = NULL;
    int64_t len = 0;
    int64_t cap = 0;

    size_t base_len = strlen(path_ptr);
    bool needs_slash = base_len > 0 && path_ptr[base_len - 1] != '/';

    struct dirent* ent;
    while ((ent = readdir(dir)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) {
            continue;
        }
        size_t name_len = strlen(ent->d_name);
        size_t full_len = base_len + (needs_slash ? 1 : 0) + name_len + 1;
        char* full_path = (char*)malloc(full_len);
        if (!full_path) continue;
        if (needs_slash) {
            snprintf(full_path, full_len, "%s/%s", path_ptr, ent->d_name);
        } else {
            snprintf(full_path, full_len, "%s%s", path_ptr, ent->d_name);
        }

        struct stat st;
        bool is_dir = false;
        bool is_file = false;
        if (lstat(full_path, &st) == 0) {
            is_dir = S_ISDIR(st.st_mode);
            is_file = S_ISREG(st.st_mode);
        }

        if (len >= cap) {
            int64_t new_cap = cap == 0 ? 8 : cap * 2;
            GdrsDirEntry* next = (buf == NULL)
                ? (GdrsDirEntry*)malloc((size_t)new_cap * sizeof(GdrsDirEntry))
                : (GdrsDirEntry*)realloc(buf, (size_t)new_cap * sizeof(GdrsDirEntry));
            if (!next) {
                free(full_path);
                continue;
            }
            buf = next;
            cap = new_cap;
        }

        GdrsDirEntry entry;
        memset(&entry, 0, sizeof(entry));
        entry.path_str = make_gdrs_string(full_path);
        entry.name_str = make_gdrs_string(ent->d_name);
        entry.is_directory = is_dir ? 1 : 0;
        entry.is_regular_file = is_file ? 1 : 0;
        buf[len++] = entry;

        free(full_path);
    }
    closedir(dir);

    vec->ptr = (uint64_t)buf;
    vec->len = len;
    vec->cap = cap;
    return 0;
}
