/* Includes the actual edited target files; RVV intrinsics are interpreted by
 * rvv_subset.h and NEON executes natively. Run on AArch64, RNE, FZ=DN=0.
 * This intentionally checks bit equality, never an epsilon comparison. */
#include <assert.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <arm_neon.h>
#include "rvv_subset.h"
#define XNN_OOB_READS
#define XNN_ARCH_ARM64 1
#define XNN_UNLIKELY(x) (x)
#define XNN_LIKELY(x) (x)
#define XNN_UNPREDICTABLE(x) (x)
#define xnn_prefetch_to_l1(x) ((void)0)
struct xnn_f32_minmax_params { struct { float min,max; } scalar; };
struct xnn_qs8_cvt_params { struct { int16_t input_zero_point; int32_t multiplier; int16_t output_zero_point; } scalar; };
#define test_neon neon_dwconv
#include "../../kernels/source/f32-dwconv-minmax.c"
#undef test_neon
#define test_rvv rvv_dwconv
#include "../../kernels/target/f32-dwconv-minmax.c"
#undef test_rvv
#define test_neon neon_spmm
#include "../../kernels/source/f32-spmm-minmax.c"
#undef test_neon
#define test_rvv rvv_spmm
#include "../../kernels/target/f32-spmm-minmax.c"
#undef test_rvv
#define test_neon neon_exp
#include "../../kernels/source/f32-raddstoreexpminusmax.c"
#undef test_neon
#define test_rvv rvv_exp
#include "../../kernels/target/f32-raddstoreexpminusmax.c"
#undef test_rvv
#define test_neon neon_cvt
#include "../../kernels/source/qs8-vcvt.c"
#undef test_neon
#define test_rvv rvv_cvt
#include "../../kernels/target/qs8-vcvt.c"
#undef test_rvv
union xnn_qs8_mul_minmax_params { struct { int8_t a_zero_point,b_zero_point; float scale; int16_t output_zero_point; int8_t output_min,output_max; } scalar; };
#define test_neon neon_mul
#include "../../kernels/source/qs8-vmul-minmax-fp32.c"
#undef test_neon
#define test_rvv rvv_mul
#include "../../kernels/target/qs8-vmul-minmax-fp32.c"
#undef test_rvv
static void equal(const char *name,const void *a,const void *b,size_t n){if(memcmp(a,b,n)){fprintf(stderr,"mismatch: %s, VLEN=%zu\n",name,test_vlen);__builtin_trap();}}
int main(void) {
  struct xnn_f32_minmax_params p={{-100,100}};
  for(test_vlen=128;test_vlen<=512;test_vlen*=2){
    for(size_t n=1;n<=65;n++){
      float in[80]={0}, w[320]={0}, a[80]={0},b[80]={0};
      const float *ptrs[3]={in,in,in};
      for(size_t j=0;j<(n+3)/4;j++)for(size_t i=0;i<4;i++)w[16*j+i]=(float)(j+1);
      neon_dwconv(n,1,ptrs,w,a,3*sizeof(void*),0,0,0,in,&p);
      rvv_dwconv(n,1,ptrs,w,b,3*sizeof(void*),0,0,0,in,&p);
      equal("dwconv packed layout",a,b,n*sizeof(float));
      for(size_t i=0;i<80;i++)in[i]=i%8==0?0:-17;
      float mx=0,sa=0,sb=0;
      neon_exp(n*sizeof(float),in,&mx,a,&sa,0);
      rvv_exp(n*sizeof(float),in,&mx,b,&sb,0);
      equal("exp lanes",a,b,n*sizeof(float));equal("exp sum",&sa,&sb,sizeof(float));
      for(size_t i=0;i<80;i++)in[i]=0x1.000002p0f;
      float weights[2]={-1,0x1.fffffcp-1f};int32_t dmap[1]={0};uint32_t nnz[1]={1};
      neon_spmm(n*sizeof(float),1,in,weights,dmap,nnz,a,n*sizeof(float),&p);
      rvv_spmm(n*sizeof(float),1,in,weights,dmap,nnz,b,n*sizeof(float),&p);
      equal("spmm fused cancellation",a,b,n*sizeof(float));
      // A nonzero map displacement must carry across source 4/2/1 strips.
      float sparse_input[160];for(size_t i=0;i<160;i++)sparse_input[i]=(float)i/8;
      dmap[0]=4;weights[0]=0;weights[1]=1;
      neon_spmm(n*sizeof(float),1,sparse_input,weights,dmap,nnz,a,n*sizeof(float),&p);
      rvv_spmm(n*sizeof(float),1,sparse_input,weights,dmap,nnz,b,n*sizeof(float),&p);
      equal("spmm pointer carry",a,b,n*sizeof(float));
      int8_t qi[80],qa[80],qb[80];memset(qi,-128,sizeof qi);
      struct xnn_qs8_cvt_params qp={{128,32768,0}};
      neon_cvt(n,qi,qa,&qp);rvv_cvt(n,qi,qb,&qp);equal("cvt saturation",qa,qb,n);
      assert(qa[0]==127);
      const uint32_t scales[]={0,0x3f800000,0xbf800000,0x4f000000,0xcf000000,0x7f800000,0xff800000,0x7fc00123,0xffc00456,0x7f800123,0xff800456};
      const int16_t zero_points[]={-32768,-128,0,1,127,32767};
      for(size_t si=0;si<sizeof(scales)/4;si++)for(size_t zi=0;zi<6;zi++){
        for(size_t j=0;j<80;j++)qi[j]=(int8_t)(j%3-1);
        union xnn_qs8_mul_minmax_params mp={{0,0,test_float(scales[si]),zero_points[zi],-128,127}};
        neon_mul(n,qi,qi,qa,&mp);rvv_mul(n,qi,qi,qb,&mp);equal("qs8 mul magic bias",qa,qb,n);
      }
    }
  }
  puts("repairs: exact native NEON / interpreted RVV agreement, sizes 1..65, VLEN 128/256/512");
}
