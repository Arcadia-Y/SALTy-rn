/* Trusted intrinsic interface for qs8-vcvt extraction; no implementations.
 * LP64, 8-bit bytes, little endian. Intrinsic effects live in Lean.
 * The matching real headers are also compiled by extract_qs8.py.
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
int8x8_t vld1_s8(const int8_t *);
void vst1_s8(int8_t *, int8x8_t);
uint32x2_t vreinterpret_u32_s8(int8x8_t);
uint16x4_t vreinterpret_u16_s8(int8x8_t);
void vst1_lane_u32(uint32_t *, uint32x2_t, const int);
void vst1_lane_u16(uint16_t *, uint16x4_t, const int);
void vst1_lane_s8(int8_t *, int8x8_t, const int);
int8x8_t vext_s8(int8x8_t, int8x8_t, const int);
int16x8_t vdupq_n_s16(int16_t);
int16x8_t vsubw_s8(int16x8_t, int8x8_t);
int16x8_t vshlq_n_s16(int16x8_t, const int);
int16x8_t vqrdmulhq_s16(int16x8_t, int16x8_t);
int16x8_t vqaddq_s16(int16x8_t, int16x8_t);
int8x8_t vqmovn_s16(int16x8_t);
size_t __riscv_vsetvl_e8m2(size_t);
vint8m2_t __riscv_vle8_v_i8m2(const int8_t *, size_t);
void __riscv_vse8_v_i8m2(int8_t *, vint8m2_t, size_t);
vint16m4_t __riscv_vsext_vf2_i16m4(vint8m2_t, size_t);
vint16m4_t __riscv_vrsub_vx_i16m4(vint16m4_t, int16_t, size_t);
vint16m4_t __riscv_vsll_vx_i16m4(vint16m4_t, size_t, size_t);
vint32m8_t __riscv_vwmul_vx_i32m8(vint16m4_t, int16_t, size_t);
vint16m4_t __riscv_vnclip_wx_i16m4(vint32m8_t, size_t, unsigned int, size_t);
vint16m4_t __riscv_vsadd_vx_i16m4(vint16m4_t, int16_t, size_t);
vint8m2_t __riscv_vnclip_wx_i8m2(vint16m4_t, size_t, unsigned int, size_t);
