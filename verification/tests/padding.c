/* ASan catches the old unmasked load before the allocated row/zero buffer.
 * Deliberately use exact allocation bases, with only right-hand tail padding. */
#include <assert.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <arm_neon.h>
#include "rvv_subset.h"
#define XNN_OOB_READS
#define XNN_UNLIKELY(x) (x)
#define XNN_UNPREDICTABLE(x) (x)
#define XNN_LIKELY(x) (x)
#define round_down_po2(x,y) ((x)&~((y)-1))
#define doz(x,y) ((x)>(y)?(x)-(y):0)
struct xnn_f32_minmax_params {struct {float min,max;} scalar;};
#define test_neon neon_conv
#include "../../kernels/source/f32-conv-hwc2chw.c"
#undef test_neon
#define test_rvv rvv_conv
#include "../../kernels/target/f32-conv-hwc2chw.c"
#undef test_rvv
int main(void){
  struct xnn_f32_minmax_params p={{-100,100}};
  for(test_vlen=128;test_vlen<=512;test_vlen*=2)
    for(size_t width=1;width<=17;width++){
      size_t height=5,ow=(width+1)/2,oh=3;
      float *in=calloc(height*width*3+16,sizeof(float));
      float *zero=calloc(width*3+16,sizeof(float));
      float *a=calloc(4*ow*oh,sizeof(float)),*b=calloc(4*ow*oh,sizeof(float));
      float weights[112];for(size_t i=0;i<112;i++)weights[i]=(float)((int)(i%5)-2)/16;
      for(size_t i=0;i<height*width*3;i++)in[i]=(float)(i%7)/8;
      neon_conv(height,width,0,oh,in,zero,weights,a,1,4,ow*4,ow*oh*4,&p);
      rvv_conv(height,width,0,oh,in,zero,weights,b,1,4,ow*4,ow*oh*4,&p);
      if(memcmp(a,b,4*ow*oh*sizeof(float))){fprintf(stderr,"conv mismatch width=%zu VLEN=%zu\n",width,test_vlen);return 1;}
      free(in);free(zero);free(a);free(b);
    }
  puts("masked convolution padding: native NEON / interpreted RVV agree for widths 1..17, VLEN 128/256/512, with allocation-boundary guards");
}
