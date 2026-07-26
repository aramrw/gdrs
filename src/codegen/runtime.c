#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <pthread.h>
#include <stdatomic.h>

static int g_argc = 0;
static char** g_argv = NULL;

extern void gdrs_main(void);

void intrinsic_panic(const char* msg) {
    fprintf(stderr, "panic: %s\n", msg ? msg : "(null)");
    fflush(stderr);
    abort();
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

// Returns all argv[1..] joined by spaces as a heap-allocated C string
const char* intrinsic_args_str(void) {
    if (g_argc <= 1) return "";
    size_t total = 0;
    for (int i = 1; i < g_argc; i++) total += strlen(g_argv[i]) + 1;
    char* buf = (char*)malloc(total + 1);
    buf[0] = '\0';
    for (int i = 1; i < g_argc; i++) {
        if (i > 1) strcat(buf, " ");
        strcat(buf, g_argv[i]);
    }
    return buf;
}

// Returns argv[idx] as a C string (or empty string if out of bounds)
const char* intrinsic_arg_at_str(int64_t idx) {
    if (idx < 0 || idx >= g_argc) return "";
    return g_argv[idx];
}


int64_t intrinsic_arg_at(int64_t idx) {
    if (idx < 0 || idx >= g_argc || !g_argv) return 0;
    return (int64_t)g_argv[idx];
}

// Print runtime output
int64_t intrinsic_log(int64_t type_tag, int64_t value_bits) {
    if (type_tag == 0) { // Int
        printf("%lld\n", (long long)value_bits);
    } else if (type_tag == 1) { // Bool
        printf("%s\n", value_bits ? "true" : "false");
    } else if (type_tag == 2) { // Str
        const char* s = (const char*)value_bits;
        if (s) {
            printf("%s\n", s);
        } else {
            printf("(null)\n");
        }
    } else if (type_tag == 3) { // Float
        double f;
        memcpy(&f, &value_bits, sizeof(double));
        printf("%g\n", f);
    } else {
        printf("%lld\n", (long long)value_bits);
    }
    fflush(stdout);
    return 0;
}

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
    targs->func = (void (*)(int64_t))func_ptr;
    targs->arg = arg;

    pthread_t thread;
    pthread_create(&thread, NULL, thread_entry, targs);
    pthread_detach(thread);
    return 0;
}

// Smart Pointer rc[T] (Reference Counted)
int64_t intrinsic_rc_new(int64_t val) {
    uint64_t* ptr = (uint64_t*)malloc(16);
    ptr[0] = 1; // ref_count
    ptr[1] = (uint64_t)val; // payload
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
            free(ptr);
        }
    }
    return 0;
}

// Smart Pointer arc[T] (Atomic Reference Counted)
int64_t intrinsic_arc_new(int64_t val) {
    _Atomic uint64_t* ptr = (_Atomic uint64_t*)malloc(16);
    atomic_init(&ptr[0], 1);
    ((uint64_t*)ptr)[1] = (uint64_t)val;
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
        free(ptr);
    }
    return 0;
}

// Iterator Intrinsics
int64_t intrinsic_iter_for_each(int64_t range_ptr_val, int64_t func_ptr) {
    if (range_ptr_val == 0 || func_ptr == 0) return 0;
    uint64_t* ptr = (uint64_t*)range_ptr_val;
    uint64_t start = ptr[0];
    uint64_t end = ptr[1];
    int64_t (*f)(int64_t) = (int64_t (*)(int64_t))func_ptr;
    for (uint64_t i = start; i < end; i++) {
        f((int64_t)i);
    }
    return 0;
}

int64_t intrinsic_iter_map(int64_t range_ptr_val, int64_t closure_ptr) {
    if (range_ptr_val == 0) return 0;
    uint64_t* src = (uint64_t*)range_ptr_val;
    uint64_t* map_iter = (uint64_t*)malloc(24);
    map_iter[0] = src[0];
    map_iter[1] = src[1];
    map_iter[2] = (uint64_t)closure_ptr;
    return (int64_t)map_iter;
}

int64_t intrinsic_map_for_each(int64_t map_iter_val, int64_t consumer_func_ptr) {
    if (map_iter_val == 0) return 0;
    uint64_t* map_iter = (uint64_t*)map_iter_val;
    uint64_t start = map_iter[0];
    uint64_t end = map_iter[1];
    int64_t (*map_fn)(int64_t) = (int64_t (*)(int64_t))map_iter[2];
    int64_t (*consumer_fn)(int64_t) = (int64_t (*)(int64_t))consumer_func_ptr;

    if (!map_fn) return 0;

    for (uint64_t i = start; i < end; i++) {
        int64_t mapped = map_fn((int64_t)i);
        if (consumer_fn) {
            consumer_fn(mapped);
        }
    }
    return 0;
}

// Vector Intrinsics
int64_t intrinsic_vec_push(int64_t vec_ptr_val, int64_t val) {
    if (vec_ptr_val == 0) return 0;
    uint64_t* vec = (uint64_t*)vec_ptr_val;
    uint64_t len = vec[1];
    uint64_t cap = vec[2];
    uint64_t* buf = (uint64_t*)vec[0];

    if (len >= cap) {
        cap = cap == 0 ? 4 : cap * 2;
        buf = (uint64_t*)realloc(buf, cap * 8);
        vec[0] = (uint64_t)buf;
        vec[2] = cap;
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
    vec[1] = len - 1;
    return (int64_t)buf[len - 1];
}

// String Concatenation
int64_t intrinsic_push_str(int64_t header_ptr_val, const char* str) {
    if (header_ptr_val == 0 || !str) return 0;
    uint64_t* header = (uint64_t*)header_ptr_val;
    char* buf = (char*)header[0];
    uint64_t len = header[1];
    uint64_t cap = header[2];

    size_t append_len = strlen(str);
    if (len + append_len + 1 > cap) {
        cap = (len + append_len + 1) * 2;
        buf = (char*)realloc(buf, cap);
        header[0] = (uint64_t)buf;
        header[2] = cap;
    }
    memcpy(buf + len, str, append_len);
    buf[len + append_len] = '\0';
    header[1] = len + append_len;
    return 0;
}
