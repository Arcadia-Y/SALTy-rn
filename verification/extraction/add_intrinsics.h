/* Trusted intrinsic interface for qs8-vadd-minmax extraction; no implementations.
 * LP64, 8-bit bytes, little endian. Intrinsic effects live in Lean.
 * The matching real headers are also compiled by extract_add.py.
 */
typedef signed char int8_t;
typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int32_t;
typedef unsigned int uint32_t;
typedef unsigned long size_t;
_Static_assert(sizeof(size_t) == 8 && sizeof(int32_t) == 4, "LP64");
typedef int8_t int8x8_t __attribute__((vector_size(8)));
typedef int8_t int8x16_t __attribute__((vector_size(16)));
typedef uint16_t uint16x4_t __attribute__((vector_size(8)));
typedef uint32_t uint32x2_t __attribute__((vector_size(8)));
/* Opaque RVV values: the model checks their active byte length at each use. */
typedef struct { unsigned char opaque; } vint8m2_t;
typedef struct { unsigned char opaque; } vint16m4_t;
typedef struct { unsigned char opaque; } vint32m8_t;
typedef int16_t int16x8_t __attribute__((vector_size(16)));
#define __RISCV_VXRM_RNU 0
#define __RISCV_VXRM_RDN 2
typedef uint16_t uint16x8_t __attribute__((vector_size(16)));
typedef struct { unsigned char opaque; } vbool4_t;
typedef int16_t int16x4_t __attribute__((vector_size(8)));
typedef int32_t int32x4_t __attribute__((vector_size(16)));
int8x8_t vld1_s8(const int8_t *);
void vst1_s8(int8_t *, int8x8_t);
uint32x2_t vreinterpret_u32_s8(int8x8_t);
uint16x4_t vreinterpret_u16_s8(int8x8_t);
void vst1_lane_u32(uint32_t *, uint32x2_t, const int);
void vst1_lane_u16(uint16_t *, uint16x4_t, const int);
void vst1_lane_s8(int8_t *, int8x8_t, const int);
int8x8_t vext_s8(int8x8_t, int8x8_t, const int);
int16x8_t vdupq_n_s16(int16_t);
int16x8_t vqaddq_s16(int16x8_t, int16x8_t);
int8x8_t vqmovn_s16(int16x8_t);
size_t __riscv_vsetvl_e8m2(size_t);
vint8m2_t __riscv_vle8_v_i8m2(const int8_t *, size_t);
void __riscv_vse8_v_i8m2(int8_t *, vint8m2_t, size_t);
vint16m4_t __riscv_vsadd_vx_i16m4(vint16m4_t, int16_t, size_t);
vint8m2_t __riscv_vnclip_wx_i8m2(vint16m4_t, size_t, unsigned int, size_t);
int8x8_t vdup_n_s8(int8_t);
int8x16_t vdupq_n_s8(int8_t);
int32x4_t vdupq_n_s32(int32_t);
int16x8_t vsubl_s8(int8x8_t, int8x8_t);
int16x4_t vget_low_s16(int16x8_t);
int16x4_t vget_high_s16(int16x8_t);
int32x4_t vmovl_s16(int16x4_t);
int32x4_t vmulq_s32(int32x4_t, int32x4_t);
int32x4_t vmlaq_s32(int32x4_t, int32x4_t, int32x4_t);
int32x4_t vrshlq_s32(int32x4_t, int32x4_t);
int16x4_t vqmovn_s32(int32x4_t);
int16x8_t vcombine_s16(int16x4_t, int16x4_t);
int8x16_t vcombine_s8(int8x8_t, int8x8_t);
int8x16_t vmaxq_s8(int8x16_t, int8x16_t);
int8x16_t vminq_s8(int8x16_t, int8x16_t);
int8x8_t vmax_s8(int8x8_t, int8x8_t);
int8x8_t vmin_s8(int8x8_t, int8x8_t);
int8x8_t vget_low_s8(int8x16_t);
void vst1q_s8(int8_t *, int8x16_t);
vint16m4_t __riscv_vwsub_vx_i16m4(vint8m2_t, int8_t, size_t);
vint32m8_t __riscv_vsext_vf2_i32m8(vint16m4_t, size_t);
vint32m8_t __riscv_vmul_vx_i32m8(vint32m8_t, int32_t, size_t);
vint32m8_t __riscv_vmacc_vx_i32m8(vint32m8_t, int32_t, vint32m8_t, size_t);
vint32m8_t __riscv_vssra_vx_i32m8(vint32m8_t, size_t, unsigned int, size_t);
vint32m8_t __riscv_vsll_vx_i32m8(vint32m8_t, size_t, size_t);
vint32m8_t __riscv_vmv_v_x_i32m8(int32_t, size_t);
vint16m4_t __riscv_vnclip_wx_i16m4(vint32m8_t, size_t, unsigned int, size_t);
vint8m2_t __riscv_vmax_vx_i8m2(vint8m2_t, int8_t, size_t);
vint8m2_t __riscv_vmin_vx_i8m2(vint8m2_t, int8_t, size_t);
