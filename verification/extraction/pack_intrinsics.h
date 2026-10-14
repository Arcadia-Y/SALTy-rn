/* Trusted declaration-only LP64 interface for x32-packw-gemm-goi. */
#define SALTY_MODEL_INTERFACE 1
#define NULL 0
typedef unsigned int uint32_t;
typedef unsigned long size_t;
typedef unsigned long uintptr_t;
typedef long ptrdiff_t;
typedef uint32_t uint32x2_t __attribute__((vector_size(8)));
typedef struct { uint32x2_t val[2]; } uint32x2x2_t;
typedef struct { unsigned char opaque; } vuint32m1_t;
typedef struct { unsigned char opaque; } vuint32m4_t;
typedef struct { unsigned char opaque; } vuint32m4x2_t;
_Static_assert(sizeof(size_t) == 8 && sizeof(uint32_t) == 4, "LP64");
uint32x2_t vld1_u32(const uint32_t *);
uint32x2_t vdup_n_u32(uint32_t);
uint32x2_t vmov_n_u32(uint32_t);
void vst1_u32(uint32_t *, uint32x2_t);
uint32x2_t vld1_lane_u32(const uint32_t *, uint32x2_t, const int);
uint32x2x2_t vld2_lane_u32(const uint32_t *, uint32x2x2_t, const int);
size_t __riscv_vsetvl_e32m4(size_t);
vuint32m4_t __riscv_vle32_v_u32m4(const uint32_t *, size_t);
vuint32m1_t __riscv_vle32_v_u32m1(const uint32_t *, size_t);
vuint32m1_t __riscv_vmv_v_x_u32m1(uint32_t, size_t);
void __riscv_vse32_v_u32m1(uint32_t *, vuint32m1_t, size_t);
void __riscv_vsse32_v_u32m4(uint32_t *, ptrdiff_t, vuint32m4_t, size_t);
vuint32m4x2_t __riscv_vcreate_v_u32m4x2(vuint32m4_t, vuint32m4_t);
void __riscv_vsseg2e32_v_u32m4x2(uint32_t *, vuint32m4x2_t, size_t);
