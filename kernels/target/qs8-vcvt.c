void test_rvv(
    size_t batch,
    const int8_t* input,
    int8_t* output,
    const struct xnn_qs8_cvt_params* restrict params) XNN_OOB_READS
{
  assert(batch != 0);
  assert(batch % sizeof(int8_t) == 0);
  assert(input != NULL);
  assert(output != NULL);

  const int16_t input_zero_point = params->scalar.input_zero_point;
  const int16_t multiplier = (int16_t) -params->scalar.multiplier;
  const int16_t output_zero_point = params->scalar.output_zero_point;

  while (batch > 0) {
    size_t vl = __riscv_vsetvl_e8m2(batch);

    vint8m2_t vx = __riscv_vle8_v_i8m2(input, vl);

    // vsubw_s8(vinput_zero_point, vx)
    vint16m4_t vx_w = __riscv_vsext_vf2_i16m4(vx, vl);
    vint16m4_t vacc = __riscv_vrsub_vx_i16m4(vx_w, input_zero_point, vl);

    // vshlq_n_s16(vacc, 7)
    vacc = __riscv_vsll_vx_i16m4(vacc, 7, vl);

    // vqrdmulhq_s16(vacc, vmultiplier)
    vint32m8_t prod = __riscv_vwmul_vx_i32m8(vacc, multiplier, vl);
    // Round the undoubled product. Doubling in i32 would wrap for
    // (-32768)*(-32768), losing SQRDMULH's positive saturation case.
    vacc = __riscv_vnclip_wx_i16m4(prod, 15, __RISCV_VXRM_RNU, vl);

    // vqaddq_s16(vacc, voutput_zero_point)
    vacc = __riscv_vsadd_vx_i16m4(vacc, output_zero_point, vl);

    // vqmovn_s16(vacc)
    vint8m2_t vy = __riscv_vnclip_wx_i8m2(vacc, 0, __RISCV_VXRM_RDN, vl);

    __riscv_vse8_v_i8m2(output, vy, vl);

    input += vl;
    output += vl;
    batch -= vl;
  }
}
