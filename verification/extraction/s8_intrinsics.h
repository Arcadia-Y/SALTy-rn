/* Trusted intrinsic interface for s8-vclamp extraction; no implementations.
 * LP64, 8-bit bytes, little endian. Intrinsic effects live in Lean.
 * The matching real headers are also compiled by extract_s8.py.
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
typedef struct { unsigned char opaque; } vint8m8_t;
int8x16_t vdupq_n_s8(int8_t);
int8x16_t vld1q_s8(const int8_t*);
int8x8_t vld1_s8(const int8_t*);
int8x16_t vmaxq_s8(int8x16_t, int8x16_t);
int8x16_t vminq_s8(int8x16_t, int8x16_t);
int8x8_t vmax_s8(int8x8_t, int8x8_t);
int8x8_t vmin_s8(int8x8_t, int8x8_t);
void vst1q_s8(int8_t*, int8x16_t);
void vst1_s8(int8_t*, int8x8_t);
int8x8_t vget_low_s8(int8x16_t);
uint32x2_t vreinterpret_u32_s8(int8x8_t);
uint16x4_t vreinterpret_u16_s8(int8x8_t);
void vst1_lane_u32(uint32_t*, uint32x2_t, const int);
void vst1_lane_u16(uint16_t*, uint16x4_t, const int);
void vst1_lane_s8(int8_t*, int8x8_t, const int);
int8x8_t vext_s8(int8x8_t, int8x8_t, const int);
size_t __riscv_vsetvl_e8m8(size_t);
vint8m8_t __riscv_vle8_v_i8m8(const int8_t*, size_t);
vint8m8_t __riscv_vmax_vx_i8m8(vint8m8_t, int8_t, size_t);
vint8m8_t __riscv_vmin_vx_i8m8(vint8m8_t, int8_t, size_t);
void __riscv_vse8_v_i8m8(int8_t*, vint8m8_t, size_t);
