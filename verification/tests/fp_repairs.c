/* Native NEON versus interpreted RVV, including original source/target files.
   This is a regression test, not a formal or binary execution proof. */
#include <assert.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <arm_neon.h>
#include "rvv_subset.h"
#define XNN_OOB_READS
#define XNN_UNLIKELY(x) (x)
struct xnn_f32_default_params {char unused;};
#define test_neon neon_vadd
#include "../../kernels/source/f32-vadd.c"
#undef test_neon
#define test_rvv rvv_vadd
#include "../../kernels/target/f32-vadd.c"
#undef test_rvv
#define test_neon neon_vsub
#include "../../kernels/source/f32-vsub.c"
#undef test_neon
#define test_rvv rvv_vsub
#include "../../kernels/target/f32-vsub.c"
#undef test_rvv
#define test_neon neon_vmul
#include "../../kernels/source/f32-vmul.c"
#undef test_neon
#define test_rvv rvv_vmul
#include "../../kernels/target/f32-vmul.c"
#undef test_rvv
#define test_neon neon_vdiv
#include "../../kernels/source/f32-vdiv.c"
#undef test_neon
#define test_rvv rvv_vdiv
#include "../../kernels/target/f32-vdiv.c"
#undef test_rvv
#define test_neon neon_vmin
#include "../../kernels/source/f32-vmin.c"
#undef test_neon
#define test_rvv rvv_vmin
#include "../../kernels/target/f32-vmin.c"
#undef test_rvv
#define test_neon neon_vmax
#include "../../kernels/source/f32-vmax.c"
#undef test_neon
#define test_rvv rvv_vmax
#include "../../kernels/target/f32-vmax.c"
#undef test_rvv
#define test_neon neon_vmulc
#include "../../kernels/source/f32-vmulc.c"
#undef test_neon
#define test_rvv rvv_vmulc
#include "../../kernels/target/f32-vmulc.c"
#undef test_rvv
#define test_neon neon_vsqrt
#include "../../kernels/source/f32-vsqrt.c"
#undef test_neon
#define test_rvv rvv_vsqrt
#include "../../kernels/target/f32-vsqrt.c"
#undef test_rvv
typedef void (*binary_fn)(size_t,const float*,const float*,float*,const struct xnn_f32_default_params*);
int main(void){
  uint64_t fpcr; __asm__("mrs %0, fpcr":"=r"(fpcr));
  assert(fpcr==0);
  const uint32_t cases[]={0,0x80000000,1,0x80000001,0x007fffff,0x807fffff,0x00800000,0x3f800000,0xbf800000,0x7f7fffff,0xff7fffff,0x7f800000,0xff800000,0x7fc00123,0xffc00456,0x7f800123,0xff800456,0x7fc00000};
  binary_fn left[]={neon_vadd,neon_vsub,neon_vmul,neon_vdiv,neon_vmin,neon_vmax,neon_vmulc};
  binary_fn right[]={rvv_vadd,rvv_vsub,rvv_vmul,rvv_vdiv,rvv_vmin,rvv_vmax,rvv_vmulc};
  const char *names[]={"add","sub","mul","div","min","max","mulc"};
  for(test_vlen=128;test_vlen<=512;test_vlen*=2)
    for(size_t op=0;op<7;op++)
      for(size_t x=0;x<sizeof(cases)/4;x++)
        for(size_t y=0;y<sizeof(cases)/4;y++)
          for(size_t n=1;n<=35;n++){
            float a[40],b[40],l[40],r[40];
            for(size_t i=0;i<40;i++){a[i]=test_float(cases[x]);b[i]=test_float(cases[y]);l[i]=r[i]=12345;}
            left[op](n*4,a,b,l,0);right[op](n*4,a,b,r,0);
            if(memcmp(l,r,sizeof l)){fprintf(stderr,"%s mismatch inputs %08x %08x n=%zu VLEN=%zu: %08x != %08x\n",names[op],cases[x],cases[y],n,test_vlen,test_bits(l[0]),test_bits(r[0]));return 1;}
          }
  for(test_vlen=128;test_vlen<=512;test_vlen*=2)
  for(size_t x=0;x<sizeof(cases)/4;x++){
    float a[8],l[8],r[8];for(size_t i=0;i<8;i++)a[i]=test_float(cases[x]);
    for(size_t n=1;n<=8;n++){neon_vsqrt(n*4,a,l,0);rvv_vsqrt(n*4,a,r,0);assert(!memcmp(l,r,n*4));}
  }
  puts("FP repairs: bit equality on 18x18 special-value pairs, lengths 1..35, VLEN 128/256/512; sqrt special values passed");
}
