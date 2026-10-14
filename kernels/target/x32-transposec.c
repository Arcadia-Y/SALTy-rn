void test_rvv(
    const uint32_t* input,
    uint32_t* output,
    size_t input_stride,
    size_t output_stride,
    size_t block_width,
    size_t block_height) XNN_OOB_READS
{
  assert(block_width == 1 || output_stride >= block_height * sizeof(uint32_t));
  assert(block_height == 1 || input_stride >= block_width * sizeof(uint32_t));

  size_t bw = block_width;
  /* The NEON do-loop executes one tile even when block_width is zero.
   * Its o1=o0 alias leaves column zero as the final output. */
  if (bw == 0) {
    bw = 1;
  }
  /* Empty-height source calls touch no memory and may use null pointers. */
  if (block_height == 0) {
    bw = 0;
  }
  while (bw > 0) {
    size_t vl = __riscv_vsetvl_e32m8(bw);
    const uint32_t* i = input;
    uint32_t* o = output;
    size_t bh = block_height;
    
    while (bh > 0) {
      vuint32m8_t v = __riscv_vle32_v_u32m8(i, vl);
      __riscv_vsse32_v_u32m8(o, output_stride, v, vl);
      
      i = (const uint32_t*) ((uintptr_t) i + input_stride);
      o += 1;
      bh -= 1;
    }
    
    input += vl;
    output = (uint32_t*) ((uintptr_t) output + vl * output_stride);
    bw -= vl;
  }
}