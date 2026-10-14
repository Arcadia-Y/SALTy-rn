/* Native source versus interpreted actual RVV target. Shift corner cases are
 * intentionally outside the usual quantizer range, but inside defined source C. */
#include <assert.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <arm_neon.h>
#include "rvv_subset.h"
#define XNN_OOB_READS
#define XNN_UNLIKELY(x) (x)
#define XNN_LIKELY(x) (x)
#define XNN_UNPREDICTABLE(x) (x)
struct xnn_qs8_add_minmax_params {
  struct { int8_t a_zero_point,b_zero_point; int32_t bias,a_multiplier,b_multiplier,shift;
    int16_t output_zero_point; int8_t output_min,output_max; } scalar;
};
#define test_neon neon_add
#include "../../kernels/source/qs8-vadd-minmax.c"
#undef test_neon
#define test_rvv rvv_add
#include "../../kernels/target/qs8-vadd-minmax.c"
#undef test_rvv
struct xnn_qu8_add_minmax_params {
  struct { uint8_t a_zero_point,b_zero_point; int32_t bias,a_multiplier,b_multiplier,shift;
    int16_t output_zero_point; uint8_t output_min,output_max; } scalar;
};
#define test_neon neon_add_u
#include "../../kernels/source/qu8-vadd-minmax.c"
#undef test_neon
#define test_rvv rvv_add_u
#include "../../kernels/target/qu8-vadd-minmax.c"
#undef test_rvv
static void compare(size_t n,struct xnn_qs8_add_minmax_params p,unsigned seed) {
  int8_t a[80],b[80],x[80],y[80];
  for(size_t j=0;j<80;j++){a[j]=(int8_t)(j*61+seed);b[j]=(int8_t)(j*103-seed);}
  memset(x,0x55,sizeof x);memset(y,0x55,sizeof y);
  neon_add(n,a,b,x,&p);rvv_add(n,a,b,y,&p);
  if(memcmp(x,y,sizeof x)){
    fprintf(stderr,"qs8 add mismatch: n=%zu shift=%d mul=%d/%d VLEN=%zu balanced=%d first=%d/%d\n",
      n,p.scalar.shift,p.scalar.a_multiplier,p.scalar.b_multiplier,test_vlen,test_balanced_vl,x[0],y[0]);
    __builtin_trap();
  }
}
static void compare_unsigned(size_t n,struct xnn_qs8_add_minmax_params p,unsigned seed) {
  uint8_t a[80],b[80],x[80],y[80];
  struct xnn_qu8_add_minmax_params u={{(uint8_t)p.scalar.a_zero_point,(uint8_t)p.scalar.b_zero_point,
    0,p.scalar.a_multiplier,p.scalar.b_multiplier,p.scalar.shift,p.scalar.output_zero_point,
    seed%2?17:0,seed%2?231:255}};
  for(size_t j=0;j<80;j++){a[j]=(uint8_t)(j*61+seed);b[j]=(uint8_t)(j*103-seed);}
  memset(x,0x55,sizeof x);memset(y,0x55,sizeof y);
  neon_add_u(n,a,b,x,&u);rvv_add_u(n,a,b,y,&u);
  if(memcmp(x,y,sizeof x)){
    fprintf(stderr,"qu8 add mismatch: n=%zu shift=%d mul=%d/%d VLEN=%zu balanced=%d first=%u/%u\n",
      n,u.scalar.shift,u.scalar.a_multiplier,u.scalar.b_multiplier,test_vlen,test_balanced_vl,x[0],y[0]);
    __builtin_trap();
  }
}
int main(void) {
  /* Check the instruction before output saturation can hide discrepancies.
   * An independent int64 reference adds the rounding bias before division. */
  const int32_t lane_values[]={INT32_MIN,INT32_MIN+1,-1073741825,-65537,-32769,
    -129,-3,-2,-1,0,1,2,3,127,32767,65535,1073741823,INT32_MAX};
  for(int raw=-512;raw<512;raw++)for(size_t i=0;i<sizeof(lane_values)/sizeof(*lane_values);i++){
    int c=(-raw)&255;if(c>=128)c-=256;
    int32_t value=lane_values[i],expected;
    if(c>=32||c<=-32)expected=0;
    else if(c>=0)expected=(uint32_t)value<<c;
    else expected=((int64_t)value+((int64_t)1<<(-c-1)))>>-c;
    int32_t actual=vgetq_lane_s32(vrshlq_s32(vdupq_n_s32(value),vdupq_n_s32(-raw)),0);
    assert(actual==expected);
  }
  /* Small concrete witness: a=1, multiplier=1, shift=32: NEON gives 0;
   * the original RVV vssra masks 32 to zero and gives 1. */
  int8_t a[8]={1},b[8]={0},x[1],y[1];
  struct xnn_qs8_add_minmax_params p={{0,0,0,1,0,32,0,-128,127}};
  neon_add(1,a,b,x,&p);rvv_add(1,a,b,y,&p);
  assert(x[0]==0);
  if(y[0]!=x[0]){fprintf(stderr,"shift=32 witness: NEON=%d RVV=%d\n",x[0],y[0]);return 1;}
  uint8_t ua[8]={1},ub[8]={0},ux[1],uy[1];
  struct xnn_qu8_add_minmax_params up={{0,0,0,1,0,32,0,0,255}};
  neon_add_u(1,ua,ub,ux,&up);rvv_add_u(1,ua,ub,uy,&up);
  assert(ux[0]==0);
  if(uy[0]!=ux[0]){fprintf(stderr,"unsigned shift=32 witness: NEON=%u RVV=%u\n",ux[0],uy[0]);return 1;}
  const int32_t multipliers[]={0,1,-1,127,-128,32768,-32768,INT32_MAX,INT32_MIN,0x40000001};
  const size_t lengths[]={1,7,8,9,15,16,17,31,32,33,65};
  const int32_t extreme_shifts[]={INT32_MIN+1,INT32_MIN+32,INT32_MAX-31,INT32_MAX};
  for(test_vlen=128;test_vlen<=512;test_vlen*=2)for(test_balanced_vl=0;test_balanced_vl<=1;test_balanced_vl++){
    for(int shift=-256;shift<256;shift++)for(size_t mi=0;mi<10;mi++){
      p.scalar.shift=shift;p.scalar.a_multiplier=multipliers[mi];p.scalar.b_multiplier=multipliers[(mi+3)%10];
      p.scalar.a_zero_point=(int8_t)(mi*37);p.scalar.b_zero_point=(int8_t)(mi*71);
      p.scalar.output_zero_point=mi%3==0?0:mi%3==1?-17:(int16_t)(mi*8191);
      p.scalar.output_min=mi%2?-107:-128;p.scalar.output_max=mi%2?89:127;
      for(size_t li=0;li<sizeof(lengths)/sizeof(*lengths);li++){compare(lengths[li],p,mi+shift);compare_unsigned(lengths[li],p,mi+shift);}
    }
    for(size_t n=1;n<=65;n++)for(size_t si=0;si<4;si++){
      p.scalar.shift=extreme_shifts[si];compare(n,p,n+si);compare_unsigned(n,p,n+si);
    }
  }
  puts("signed and unsigned quantized add: native NEON / interpreted RVV agreement, every low-byte shift, extreme raw shifts, both VL schedules");
}
