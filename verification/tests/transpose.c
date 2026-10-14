/* Actual source/target word-copy kernels, with full-buffer and scalar-oracle
 * comparison. This is bounded native/interpreted testing, not a Lean theorem. */
#include <assert.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <arm_neon.h>
#include "rvv_subset.h"
#define XNN_OOB_READS
#define XNN_UNPREDICTABLE(x) (x)
static size_t round_down_po2(size_t n,size_t q) { return n & -q; }
static size_t doz(size_t a,size_t b) { return a>b ? a-b : 0; }
#define test_neon neon_transpose
#include "../../kernels/source/x32-transposec.c"
#undef test_neon
#define test_rvv rvv_transpose
#include "../../kernels/target/x32-transposec.c"
#undef test_rvv

int main(void) {
  for(test_vlen=128;test_vlen<=512;test_vlen*=2)
  for(test_balanced_vl=0;test_balanced_vl<2;test_balanced_vl++)
  for(test_reverse_strided=0;test_reverse_strided<2;test_reverse_strided++)
  for(size_t width=0;width<=65;width++)
  for(size_t height=0;height<=9;height++)
  for(size_t pad=0;pad<=3;pad+=3) {
    size_t is=width+pad, os=height+pad;
    size_t columns=width ? width : 1;
    size_t in_count=is*(height+1)+2, out_count=os*columns+8;
    uint32_t *in=malloc(4*in_count), *a=malloc(4*out_count);
    uint32_t *b=malloc(4*out_count), *expected=malloc(4*out_count);
    assert(in && a && b && expected);
    for(size_t k=0;k<in_count;k++) in[k]=(uint32_t)(k*0x9e3779b9u)^0x7fc01234u;
    for(size_t k=0;k<out_count;k++) a[k]=b[k]=expected[k]=0xdeadbeefu;
    for(size_t r=0;r<height;r++) for(size_t c=0;c<columns;c++)
      expected[4+c*os+r]=in[r*is+c];
    neon_transpose(in,a+4,4*is,4*os,width,height);
    rvv_transpose(in,b+4,4*is,4*os,width,height);
    if(memcmp(a,expected,4*out_count) || memcmp(b,expected,4*out_count)) {
      fprintf(stderr,"transpose mismatch %zux%zu pad=%zu VLEN=%zu balanced=%d reverse=%d\n",
        width,height,pad,test_vlen,test_balanced_vl,test_reverse_strided); return 1;
    }
    free(in);free(a);free(b);free(expected);
  }
  /* Regression: the source do-loop copies column zero even at width zero. */
  uint32_t in[2]={7,9}, a[2]={0,0}, b[2]={0,0};
  neon_transpose(in,a,8,4,0,1);
  rvv_transpose(in,b,8,4,0,1);
  assert(a[0]==7 && b[0]==7);
  neon_transpose(NULL,NULL,0,0,0,0);
  rvv_transpose(NULL,NULL,0,0,0,0);
  neon_transpose(NULL,NULL,12,0,3,0);
  rvv_transpose(NULL,NULL,12,0,3,0);
  puts("transpose: widths 0..65, heights 0..9, tight/padded strides, VLEN 128/256/512, two legal VL policies and both store orders; zero-width repair passed");
}
