/* Trusted declaration interface for x32-transposec. No executable intrinsics. */
#define SALTY_MODEL_INTERFACE 1
typedef unsigned int uint32_t;
typedef unsigned long size_t;
typedef unsigned long uintptr_t;
typedef long ptrdiff_t;
typedef uint32_t uint32x2_t __attribute__((vector_size(8)));
typedef struct { uint32x2_t val[2]; } uint32x2x2_t;
typedef struct { unsigned char opaque; } vuint32m8_t;
_Static_assert(sizeof(size_t) == 8 && sizeof(uint32_t) == 4, "LP64");
uint32x2_t vld1_u32(const uint32_t*);
uint32x2_t vmov_n_u32(uint32_t);
uint32x2x2_t vzip_u32(uint32x2_t, uint32x2_t);
void vst1_u32(uint32_t*, uint32x2_t);
void vst1_lane_u32(uint32_t*, uint32x2_t, const int);
size_t __riscv_vsetvl_e32m8(size_t);
vuint32m8_t __riscv_vle32_v_u32m8(const uint32_t*, size_t);
void __riscv_vsse32_v_u32m8(uint32_t*, ptrdiff_t, vuint32m8_t, size_t);
size_t round_down_po2(size_t, size_t);
size_t doz(size_t, size_t);
