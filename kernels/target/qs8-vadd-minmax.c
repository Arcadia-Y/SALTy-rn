void test_rvv(
    size_t batch,
    const int8_t* input_a,
    const int8_t* input_b,
    int8_t* output,
    const struct xnn_qs8_add_minmax_params* restrict params) XNN_OOB_READS
{
  assert(batch != 0);
  assert(batch % sizeof(int8_t) == 0);
  assert(input_a != NULL);
  assert(input_b != NULL);
  assert(output != NULL);

  const int8_t a_zero_point = params->scalar.a_zero_point;
  const int8_t b_zero_point = params->scalar.b_zero_point;
  const int32_t a_multiplier = params->scalar.a_multiplier;
  const int32_t b_multiplier = params->scalar.b_multiplier;
  /* NEON SRSHL reads a signed low byte of -shift. RVV VSSRA instead
   * masks to five bits and only shifts right. Decode the NEON count
   * explicitly; unsigned negation also avoids introducing C overflow. */
  const uint32_t shift_byte = (0u - (uint32_t)params->scalar.shift) & 255u;
  const int32_t shift = (int32_t)shift_byte - (shift_byte >= 128u ? 256 : 0);
  const int16_t output_zero_point = params->scalar.output_zero_point;
  const int8_t output_min = params->scalar.output_min;
  const int8_t output_max = params->scalar.output_max;

  while (batch > 0) {
    size_t vl = __riscv_vsetvl_e8m2(batch);

    vint8m2_t va = __riscv_vle8_v_i8m2(input_a, vl);
    vint8m2_t vb = __riscv_vle8_v_i8m2(input_b, vl);

    vint16m4_t vxa = __riscv_vwsub_vx_i16m4(va, a_zero_point, vl);
    vint16m4_t vxb = __riscv_vwsub_vx_i16m4(vb, b_zero_point, vl);

    vint32m8_t vxa32 = __riscv_vsext_vf2_i32m8(vxa, vl);
    vint32m8_t vxb32 = __riscv_vsext_vf2_i32m8(vxb, vl);

    vint32m8_t vacc = __riscv_vmul_vx_i32m8(vxa32, a_multiplier, vl);
    vacc = __riscv_vmacc_vx_i32m8(vacc, b_multiplier, vxb32, vl);

    if (shift <= -32 || shift >= 32) {
      /* A rounded signed right shift by 32 or more, or a left shift
       * by 32 or more, produces zero in every 32-bit lane. */
      vacc = __riscv_vmv_v_x_i32m8(0, vl);
    } else if (shift < 0) {
      vacc = __riscv_vssra_vx_i32m8(vacc, (size_t)-shift, __RISCV_VXRM_RNU, vl);
    } else {
      vacc = __riscv_vsll_vx_i32m8(vacc, (size_t)shift, vl);
    }

    vint16m4_t vacc16 = __riscv_vnclip_wx_i16m4(vacc, 0, __RISCV_VXRM_RDN, vl);
    vacc16 = __riscv_vsadd_vx_i16m4(vacc16, output_zero_point, vl);

    vint8m2_t vout = __riscv_vnclip_wx_i8m2(vacc16, 0, __RISCV_VXRM_RDN, vl);

    vout = __riscv_vmax_vx_i8m2(vout, output_min, vl);
    vout = __riscv_vmin_vx_i8m2(vout, output_max, vl);

    __riscv_vse8_v_i8m2(output, vout, vl);

    input_a += vl;
    input_b += vl;
    output += vl;
    batch -= vl;
  }
}
