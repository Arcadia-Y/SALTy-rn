void test_rvv(
    size_t batch,
    const float* input_a,
    const float* input_b,
    float* output,
    const struct xnn_f32_default_params* restrict params)
{
  assert(batch != 0);
  assert(batch % sizeof(float) == 0);
  assert(input_a != NULL);
  assert(input_b != NULL);
  assert(output != NULL);

  size_t n = batch / sizeof(float);
  while (n > 0) {
    size_t vl = __riscv_vsetvl_e32m8(n);
    vfloat32m8_t va = __riscv_vle32_v_f32m8(input_a, vl);
    vfloat32m8_t vb = __riscv_vle32_v_f32m8(input_b, vl);
    
    vfloat32m8_t vacc = __riscv_vfdiv_vv_f32m8(va, vb, vl);
    
    // AArch64 FPCR.DN=0: propagate the first signaling NaN, otherwise
    // the first quiet NaN, retaining sign/payload and setting the quiet bit.
    // RVV arithmetic canonicalizes NaNs and vfmin/vfmax prefer numbers.
    const vuint32m8_t ua = __riscv_vreinterpret_v_f32m8_u32m8(va);
    const vuint32m8_t ub = __riscv_vreinterpret_v_f32m8_u32m8(vb);
    const vuint32m8_t aa = __riscv_vand_vx_u32m8(ua, UINT32_C(0x7fffffff), vl);
    const vuint32m8_t ab = __riscv_vand_vx_u32m8(ub, UINT32_C(0x7fffffff), vl);
    const vbool4_t na = __riscv_vmsgtu_vx_u32m8_b4(aa, UINT32_C(0x7f800000), vl);
    const vbool4_t nb = __riscv_vmsgtu_vx_u32m8_b4(ab, UINT32_C(0x7f800000), vl);
    const vbool4_t sa = __riscv_vmand_mm_b4(na,
        __riscv_vmsltu_vx_u32m8_b4(aa, UINT32_C(0x7fc00000), vl), vl);
    const vbool4_t sb = __riscv_vmand_mm_b4(nb,
        __riscv_vmsltu_vx_u32m8_b4(ab, UINT32_C(0x7fc00000), vl), vl);
    const vuint32m8_t qa = __riscv_vor_vx_u32m8(ua, UINT32_C(0x00400000), vl);
    const vuint32m8_t qb = __riscv_vor_vx_u32m8(ub, UINT32_C(0x00400000), vl);
    vuint32m8_t result = __riscv_vreinterpret_v_f32m8_u32m8(vacc);
    result = __riscv_vmerge_vvm_u32m8(result, qb, nb, vl);
    result = __riscv_vmerge_vvm_u32m8(result, qa, na, vl);
    result = __riscv_vmerge_vvm_u32m8(result, qb, sb, vl);
    result = __riscv_vmerge_vvm_u32m8(result, qa, sa, vl);
    vacc = __riscv_vreinterpret_v_u32m8_f32m8(result);

    __riscv_vse32_v_f32m8(output, vacc, vl);
    
    input_a += vl;
    input_b += vl;
    output += vl;
    n -= vl;
  }
}