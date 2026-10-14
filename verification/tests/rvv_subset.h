/* Test interpreter for the repaired kernels' RVV subset. This is regression
 * evidence, not an ISA emulator or a proof of compiled RISC-V execution.
 * Tail-undisturbed addition is modeled explicitly; other tails are unused. */
#include <math.h>
#include <string.h>
static size_t test_vlen = 128;
static int test_balanced_vl = 0;
static int test_reverse_strided = 0;
typedef struct { float v[128]; } test_fvec;
typedef struct { int32_t v[128]; } test_ivec;
typedef struct { unsigned char v[128]; } test_mask;
typedef test_fvec vfloat32m4_t;
typedef test_fvec vfloat32m8_t;
typedef test_ivec vint32m4_t;
typedef test_ivec vint32m8_t;
typedef test_ivec vint16m4_t;
typedef test_ivec vint8m2_t;
typedef test_mask vbool8_t;
#define __RISCV_VXRM_RNU 0
#define __RISCV_VXRM_RDN 2
static size_t test_vl(size_t n, size_t cap) {
  if (test_balanced_vl && n > cap && n < 2 * cap) return (n + 1) / 2;
  return n < cap ? n : cap;
}
static size_t __riscv_vsetvl_e32m4(size_t n) { return test_vl(n, test_vlen / 8); }
static size_t __riscv_vsetvl_e32m8(size_t n) { return test_vl(n, test_vlen / 4); }
static size_t __riscv_vsetvl_e8m2(size_t n) { return test_vl(n, test_vlen / 4); }
static float test_canonical(float x);
static float test_min(float a,float b);
static float test_max(float a,float b);
#define FLOAT_OPS(M) \
static test_fvec __riscv_vle32_v_f32m##M(const float *p,size_t n) { test_fvec r={0}; for(size_t i=0;i<n;i++)r.v[i]=p[i]; return r; } \
static void __riscv_vse32_v_f32m##M(float *p,test_fvec a,size_t n) { for(size_t i=0;i<n;i++)p[i]=a.v[i]; } \
static test_fvec __riscv_vfmv_v_f_f32m##M(float a,size_t n) { test_fvec r={0};for(size_t i=0;i<n;i++)r.v[i]=a;return r;} \
static test_fvec __riscv_vfadd_vv_f32m##M(test_fvec a,test_fvec b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_canonical(a.v[i]+b.v[i]);return a;} \
static test_fvec __riscv_vfmul_vv_f32m##M(test_fvec a,test_fvec b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_canonical(a.v[i]*b.v[i]);return a;} \
static test_fvec __riscv_vfmul_vf_f32m##M(test_fvec a,float b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_canonical(a.v[i]*b);return a;} \
static test_fvec __riscv_vfmin_vf_f32m##M(test_fvec a,float b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_min(a.v[i],b);return a;} \
static test_fvec __riscv_vfmax_vf_f32m##M(test_fvec a,float b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_max(a.v[i],b);return a;} \
static test_fvec __riscv_vfmacc_vv_f32m##M(test_fvec c,test_fvec a,test_fvec b,size_t n){for(size_t i=0;i<n;i++)c.v[i]=test_canonical(fmaf(a.v[i],b.v[i],c.v[i]));return c;} \
static test_fvec __riscv_vfmacc_vf_f32m##M(test_fvec c,float a,test_fvec b,size_t n){for(size_t i=0;i<n;i++)c.v[i]=test_canonical(fmaf(a,b.v[i],c.v[i]));return c;}
FLOAT_OPS(4)
FLOAT_OPS(8)
static test_fvec __riscv_vfsub_vf_f32m4(test_fvec a,float b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_canonical(a.v[i]-b);return a;}
static test_fvec __riscv_vfmadd_vf_f32m4(test_fvec a,float b,test_fvec c,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_canonical(fmaf(a.v[i],b,c.v[i]));return a;}
static test_ivec __riscv_vreinterpret_v_f32m4_i32m4(test_fvec a){test_ivec r;memcpy(&r,&a,sizeof r);return r;}
static test_fvec __riscv_vreinterpret_v_i32m4_f32m4(test_ivec a){test_fvec r;memcpy(&r,&a,sizeof r);return r;}
static test_ivec __riscv_vsll_vx_i32m4(test_ivec a,unsigned k,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(int32_t)((uint32_t)a.v[i]<<k);return a;}
static test_mask __riscv_vmflt_vf_f32m4_b8(test_fvec a,float b,size_t n){test_mask r={0};for(size_t i=0;i<n;i++)r.v[i]=a.v[i]<b;return r;}
static test_fvec __riscv_vfmerge_vfm_f32m4(test_fvec a,float b,test_mask mask,size_t n){for(size_t i=0;i<n;i++)if(mask.v[i])a.v[i]=b;return a;}
static test_fvec __riscv_vfadd_vv_f32m4_tu(test_fvec old,test_fvec a,test_fvec b,size_t n){for(size_t i=0;i<n;i++)old.v[i]=test_canonical(a.v[i]+b.v[i]);return old;}
static test_ivec __riscv_vle8_v_i8m2(const int8_t *p,size_t n){test_ivec r={0};for(size_t i=0;i<n;i++)r.v[i]=p[i];return r;}
static test_ivec __riscv_vsext_vf2_i16m4(test_ivec a,size_t n){(void)n;return a;}
static test_ivec __riscv_vrsub_vx_i16m4(test_ivec a,int16_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(int16_t)(b-a.v[i]);return a;}
static test_ivec __riscv_vsll_vx_i16m4(test_ivec a,unsigned k,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(int16_t)((uint16_t)a.v[i]<<k);return a;}
static test_ivec __riscv_vwmul_vx_i32m8(test_ivec a,int16_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]*=b;return a;}
static test_ivec __riscv_vwsub_vx_i16m4(test_ivec a,int8_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]-=b;return a;}
static test_ivec __riscv_vsext_vf2_i32m8(test_ivec a,size_t n){(void)n;return a;}
static test_ivec __riscv_vmul_vx_i32m8(test_ivec a,int32_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(uint32_t)a.v[i]*(uint32_t)b;return a;}
static test_ivec __riscv_vmacc_vx_i32m8(test_ivec acc,int32_t b,test_ivec a,size_t n){for(size_t i=0;i<n;i++)acc.v[i]=(uint32_t)acc.v[i]+(uint32_t)a.v[i]*(uint32_t)b;return acc;}
static test_ivec __riscv_vssra_vx_i32m8(test_ivec a,size_t k,unsigned mode,size_t n){assert(mode==__RISCV_VXRM_RNU);k&=31;for(size_t i=0;i<n;i++)a.v[i]=((int64_t)a.v[i]+(k?((int64_t)1<<(k-1)):0))>>k;return a;}
static test_ivec __riscv_vsll_vx_i32m8(test_ivec a,size_t k,size_t n){k&=31;for(size_t i=0;i<n;i++)a.v[i]=(uint32_t)a.v[i]<<k;return a;}
static test_ivec __riscv_vmv_v_x_i32m8(int32_t x,size_t n){test_ivec r={0};for(size_t i=0;i<n;i++)r.v[i]=x;return r;}
static int32_t test_sat(int64_t x,int64_t lo,int64_t hi){return (int32_t)(x<lo?lo:x>hi?hi:x);}
static test_ivec __riscv_vnclip_wx_i16m4(test_ivec a,unsigned k,unsigned mode,size_t n){assert(mode==0||(mode==2&&k==0));for(size_t i=0;i<n;i++)a.v[i]=test_sat(((int64_t)a.v[i]+(k?((int64_t)1<<(k-1)):0))>>k,-32768,32767);return a;}
static test_ivec __riscv_vsadd_vx_i16m4(test_ivec a,int16_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_sat(a.v[i]+b,-32768,32767);return a;}
static test_ivec __riscv_vnclip_wx_i8m2(test_ivec a,unsigned k,unsigned mode,size_t n){assert(k==0&&mode==2);for(size_t i=0;i<n;i++)a.v[i]=test_sat(a.v[i],-128,127);return a;}
static void __riscv_vse8_v_i8m2(int8_t *p,test_ivec a,size_t n){for(size_t i=0;i<n;i++)p[i]=(int8_t)a.v[i];}
/* Bit-level NaN/min/max behavior of RVV for the pointwise regression tests. */
typedef test_ivec vuint32m8_t;
typedef test_mask vbool4_t;
static uint32_t test_bits(float x){uint32_t u;memcpy(&u,&x,4);return u;}
static float test_float(uint32_t u){float x;memcpy(&x,&u,4);return x;}
static int test_nan(float x){return (test_bits(x)&0x7fffffff)>0x7f800000;}
static float test_canonical(float x){return test_nan(x)?test_float(0x7fc00000):x;}
static test_ivec __riscv_vreinterpret_v_f32m8_u32m8(test_fvec a){test_ivec r;memcpy(&r,&a,sizeof r);return r;}
static test_fvec __riscv_vreinterpret_v_u32m8_f32m8(test_ivec a){test_fvec r;memcpy(&r,&a,sizeof r);return r;}
static test_ivec __riscv_vand_vx_u32m8(test_ivec a,uint32_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(uint32_t)a.v[i]&b;return a;}
static test_ivec __riscv_vor_vx_u32m8(test_ivec a,uint32_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(uint32_t)a.v[i]|b;return a;}
static test_mask __riscv_vmsgtu_vx_u32m8_b4(test_ivec a,uint32_t b,size_t n){test_mask r={0};for(size_t i=0;i<n;i++)r.v[i]=(uint32_t)a.v[i]>b;return r;}
static test_mask __riscv_vmsltu_vx_u32m8_b4(test_ivec a,uint32_t b,size_t n){test_mask r={0};for(size_t i=0;i<n;i++)r.v[i]=(uint32_t)a.v[i]<b;return r;}
static test_mask __riscv_vmand_mm_b4(test_mask a,test_mask b,size_t n){for(size_t i=0;i<n;i++)a.v[i]&=b.v[i];return a;}
static test_ivec __riscv_vmerge_vvm_u32m8(test_ivec a,test_ivec b,test_mask m,size_t n){for(size_t i=0;i<n;i++)if(m.v[i])a.v[i]=b.v[i];return a;}
static float test_min(float a,float b){if(test_nan(a))return test_canonical(b);if(test_nan(b))return a;if(a==0&&b==0)return test_float(test_bits(a)|test_bits(b));return a<b?a:b;}
static float test_max(float a,float b){if(test_nan(a))return test_canonical(b);if(test_nan(b))return a;if(a==0&&b==0)return test_float(test_bits(a)&test_bits(b));return a>b?a:b;}
static test_fvec __riscv_vfsub_vv_f32m8(test_fvec a,test_fvec b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_canonical(a.v[i]-b.v[i]);return a;}
static test_fvec __riscv_vfdiv_vv_f32m8(test_fvec a,test_fvec b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_canonical(a.v[i]/b.v[i]);return a;}
static test_fvec __riscv_vfmin_vv_f32m8(test_fvec a,test_fvec b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_min(a.v[i],b.v[i]);return a;}
static test_fvec __riscv_vfmax_vv_f32m8(test_fvec a,test_fvec b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_max(a.v[i],b.v[i]);return a;}
static test_fvec __riscv_vfsqrt_v_f32m8(test_fvec a,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_canonical(sqrtf(a.v[i]));return a;}
static test_ivec __riscv_vsub_vx_i16m4(test_ivec a,int16_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(int16_t)(a.v[i]-b);return a;}
static test_ivec __riscv_vwmul_vv_i32m8(test_ivec a,test_ivec b,size_t n){for(size_t i=0;i<n;i++)a.v[i]*=b.v[i];return a;}
static test_fvec __riscv_vfcvt_f_x_v_f32m8(test_ivec a,size_t n){test_fvec r={0};for(size_t i=0;i<n;i++)r.v[i]=(float)a.v[i];return r;}
static test_ivec __riscv_vmv_v_x_u32m8(uint32_t x,size_t n){test_ivec r={0};for(size_t i=0;i<n;i++)r.v[i]=x;return r;}
static test_fvec __riscv_vfadd_vf_f32m8(test_fvec a,float b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_canonical(a.v[i]+b);return a;}
static test_ivec __riscv_vreinterpret_v_f32m8_i32m8(test_fvec a){test_ivec r;memcpy(&r,&a,sizeof r);return r;}
static test_ivec __riscv_vssub_vx_i32m8(test_ivec a,int32_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=test_sat((int64_t)a.v[i]-b,INT32_MIN,INT32_MAX);return a;}
static test_ivec __riscv_vmax_vx_i8m2(test_ivec a,int8_t b,size_t n){for(size_t i=0;i<n;i++)if(a.v[i]<b)a.v[i]=b;return a;}
static test_ivec __riscv_vmin_vx_i8m2(test_ivec a,int8_t b,size_t n){for(size_t i=0;i<n;i++)if(a.v[i]>b)a.v[i]=b;return a;}

static test_ivec __riscv_vreinterpret_v_u32m8_i32m8(test_ivec a){return a;}
/* m1 operations used by the masked-padding regression. */
typedef test_fvec vfloat32m1_t;
typedef test_ivec vint32m1_t;
typedef test_ivec vuint32m1_t;
typedef test_mask vbool32_t;
FLOAT_OPS(1)
static size_t __riscv_vsetvl_e32m1(size_t n){return test_vl(n,test_vlen/32);}
static test_ivec __riscv_vid_v_u32m1(size_t n){test_ivec r={0};for(size_t i=0;i<n;i++)r.v[i]=i;return r;}
static test_ivec __riscv_vadd_vx_u32m1(test_ivec a,uint32_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(uint32_t)a.v[i]+b;return a;}
static test_ivec __riscv_vmul_vx_u32m1(test_ivec a,uint32_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(uint32_t)a.v[i]*b;return a;}
static test_ivec __riscv_vreinterpret_v_u32m1_i32m1(test_ivec a){return a;}
static test_ivec __riscv_vsub_vx_i32m1(test_ivec a,int32_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(uint32_t)a.v[i]-(uint32_t)b;return a;}
static test_ivec __riscv_vadd_vx_i32m1(test_ivec a,int32_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(uint32_t)a.v[i]+(uint32_t)b;return a;}
static test_mask __riscv_vmsge_vx_i32m1_b32(test_ivec a,int32_t b,size_t n){test_mask r={0};for(size_t i=0;i<n;i++)r.v[i]=a.v[i]>=b;return r;}
static test_mask __riscv_vmslt_vx_i32m1_b32(test_ivec a,int32_t b,size_t n){test_mask r={0};for(size_t i=0;i<n;i++)r.v[i]=a.v[i]<b;return r;}
static test_mask __riscv_vmand_mm_b32(test_mask a,test_mask b,size_t n){for(size_t i=0;i<n;i++)a.v[i]&=b.v[i];return a;}
static test_fvec __riscv_vlse32_v_f32m1_tumu(test_mask mask,test_fvec old,const float *base,ptrdiff_t stride,size_t n){for(size_t i=0;i<n;i++)if(mask.v[i])memcpy(&old.v[i],(const void*)((uintptr_t)base+i*stride),4);return old;}

/* Word-copy operations for transpose regressions. Reverse order models another
 * permitted strided-store ordering; tests use disjoint active destinations. */
static test_ivec __riscv_vle32_v_u32m8(const uint32_t *p,size_t n) {
  test_ivec r={0}; for(size_t i=0;i<n;i++) memcpy(&r.v[i],p+i,4); return r;
}
static void __riscv_vsse32_v_u32m8(uint32_t *p,ptrdiff_t stride,test_ivec x,size_t n) {
  for(size_t k=0;k<n;k++) {
    size_t i=test_reverse_strided ? n-1-k : k;
    memcpy((unsigned char*)p+(ptrdiff_t)i*stride,&x.v[i],4);
  }
}

/* Unsigned-byte quantized addition; intermediate unsigned halfwords retain
 * their 16-bit representation until the explicit signed reinterpret. */
typedef test_ivec vuint8m2_t;
typedef test_ivec vuint16m4_t;
static test_ivec __riscv_vle8_v_u8m2(const uint8_t *p,size_t n){test_ivec r={0};for(size_t i=0;i<n;i++)r.v[i]=p[i];return r;}
static test_ivec __riscv_vwsubu_vx_u16m4(test_ivec a,uint8_t b,size_t n){for(size_t i=0;i<n;i++)a.v[i]=(uint16_t)(a.v[i]-b);return a;}
static test_ivec __riscv_vreinterpret_v_u16m4_i16m4(test_ivec a){for(size_t i=0;i<128;i++)a.v[i]=(int16_t)a.v[i];return a;}
static test_ivec __riscv_vreinterpret_v_i16m4_u16m4(test_ivec a){for(size_t i=0;i<128;i++)a.v[i]=(uint16_t)a.v[i];return a;}
static test_ivec __riscv_vmax_vx_i16m4(test_ivec a,int16_t b,size_t n){for(size_t i=0;i<n;i++)if(a.v[i]<b)a.v[i]=b;return a;}
static test_ivec __riscv_vnclipu_wx_u8m2(test_ivec a,unsigned k,unsigned mode,size_t n){assert(k==0&&mode==__RISCV_VXRM_RDN);for(size_t i=0;i<n;i++)a.v[i]=test_sat((uint16_t)a.v[i],0,255);return a;}
static test_ivec __riscv_vmaxu_vx_u8m2(test_ivec a,uint8_t b,size_t n){for(size_t i=0;i<n;i++)if(a.v[i]<b)a.v[i]=b;return a;}
static test_ivec __riscv_vminu_vx_u8m2(test_ivec a,uint8_t b,size_t n){for(size_t i=0;i<n;i++)if(a.v[i]>b)a.v[i]=b;return a;}
static void __riscv_vse8_v_u8m2(uint8_t *p,test_ivec a,size_t n){for(size_t i=0;i<n;i++)p[i]=(uint8_t)a.v[i];}
