void test_rvv(
    size_t batch,
    const float* input,
    float* output,
    const struct xnn_f32_default_params* unused_params)
{
  assert(batch != 0);
  assert(batch % sizeof(float) == 0);
  assert(input != NULL);
  assert(output != NULL);

  size_t n = batch / sizeof(float);
  while (n > 0) {
    size_t vl = __riscv_vsetvl_e32m8(n);
    vfloat32m8_t vx = __riscv_vle32_v_f32m8(input, vl);
    vfloat32m8_t vy = __riscv_vfsqrt_v_f32m8(vx, vl);
    // Restore AArch64's quieted input NaN (FPCR.DN=0).
    vuint32m8_t ux = __riscv_vreinterpret_v_f32m8_u32m8(vx);
    vuint32m8_t ax = __riscv_vand_vx_u32m8(ux, UINT32_C(0x7fffffff), vl);
    vbool4_t nan = __riscv_vmsgtu_vx_u32m8_b4(ax, UINT32_C(0x7f800000), vl);
    vuint32m8_t quiet = __riscv_vor_vx_u32m8(ux, UINT32_C(0x00400000), vl);
    vuint32m8_t result = __riscv_vreinterpret_v_f32m8_u32m8(vy);
    result = __riscv_vmerge_vvm_u32m8(result, quiet, nan, vl);
    vy = __riscv_vreinterpret_v_u32m8_f32m8(result);
    __riscv_vse32_v_f32m8(output, vy, vl);
    input += vl;
    output += vl;
    n -= vl;
  }
}