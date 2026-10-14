void test_rvv(
    size_t batch,
    const uint8_t* input_a,
    const uint8_t* input_b,
    uint8_t* output,
    const struct xnn_qu8_add_minmax_params* restrict params) XNN_OOB_READS
{
  assert(batch != 0);
  assert(batch % sizeof(uint8_t) == 0);
  assert(input_a != NULL);
  assert(input_b != NULL);
  assert(output != NULL);

  const uint8_t a_zero_point = params->scalar.a_zero_point;
  const uint8_t b_zero_point = params->scalar.b_zero_point;
  const int32_t a_multiplier = params->scalar.a_multiplier;
  const int32_t b_multiplier = params->scalar.b_multiplier;
  /* NEON SRSHL uses the signed low byte of the negated raw count.
   * RVV shifts mask to five bits, so decode direction and wide counts first.
   * Unsigned negation keeps this scalar calculation defined for every bit pattern. */
  const uint32_t shift_byte = (0u - (uint32_t)params->scalar.shift) & 255u;
  const int32_t shift = (int32_t)shift_byte - (shift_byte >= 128u ? 256 : 0);
  const int16_t output_zero_point = params->scalar.output_zero_point;
  const uint8_t output_min = params->scalar.output_min;
  const uint8_t output_max = params->scalar.output_max;

  while (batch > 0) {
    size_t vl = __riscv_vsetvl_e8m2(batch);

    vuint8m2_t va = __riscv_vle8_v_u8m2(input_a, vl);
    vuint8m2_t vb = __riscv_vle8_v_u8m2(input_b, vl);

    // Widen to 16-bit and subtract zero points
    vuint16m4_t vxa_u = __riscv_vwsubu_vx_u16m4(va, a_zero_point, vl);
    vint16m4_t vxa = __riscv_vreinterpret_v_u16m4_i16m4(vxa_u);

    vuint16m4_t vxb_u = __riscv_vwsubu_vx_u16m4(vb, b_zero_point, vl);
    vint16m4_t vxb = __riscv_vreinterpret_v_u16m4_i16m4(vxb_u);

    // Widen to 32-bit and multiply-accumulate
    vint32m8_t vxa32 = __riscv_vsext_vf2_i32m8(vxa, vl);
    vint32m8_t vacc = __riscv_vmul_vx_i32m8(vxa32, a_multiplier, vl);

    vint32m8_t vxb32 = __riscv_vsext_vf2_i32m8(vxb, vl);
    vacc = __riscv_vmacc_vx_i32m8(vacc, b_multiplier, vxb32, vl);

    if (shift <= -32 || shift >= 32) {
      vacc = __riscv_vmv_v_x_i32m8(0, vl);
    } else if (shift < 0) {
      vacc = __riscv_vssra_vx_i32m8(vacc, (size_t)-shift, __RISCV_VXRM_RNU, vl);
    } else {
      vacc = __riscv_vsll_vx_i32m8(vacc, (size_t)shift, vl);
    }

    // Saturating narrow to 16-bit
    vint16m4_t vacc16 = __riscv_vnclip_wx_i16m4(vacc, (size_t)0, __RISCV_VXRM_RDN, vl);

    // Saturating add output zero point
    vacc16 = __riscv_vsadd_vx_i16m4(vacc16, output_zero_point, vl);

    // Signed-to-unsigned saturating narrow to 8-bit
    vacc16 = __riscv_vmax_vx_i16m4(vacc16, (int16_t)0, vl);
    vuint16m4_t vacc16_u = __riscv_vreinterpret_v_i16m4_u16m4(vacc16);
    vuint8m2_t vout = __riscv_vnclipu_wx_u8m2(vacc16_u, (size_t)0, __RISCV_VXRM_RDN, vl);

    // Clamp to min/max
    vout = __riscv_vmaxu_vx_u8m2(vout, output_min, vl);
    vout = __riscv_vminu_vx_u8m2(vout, output_max, vl);

    __riscv_vse8_v_u8m2(output, vout, vl);

    input_a += vl;
    input_b += vl;
    output += vl;
    batch -= vl;
  }
}