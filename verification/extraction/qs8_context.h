/* Fixed LP64 context; assertions remain checked model operations. */
#define NULL ((void*)0)
#define XNN_OOB_READS
#define XNN_UNLIKELY(x) (x)
extern void salty_assert(int);
#define assert(x) salty_assert(!!(x))
struct xnn_qs8_cvt_params {
  struct {
    int16_t input_zero_point;
    int32_t multiplier;
    int16_t output_zero_point;
  } scalar;
};
_Static_assert(sizeof(struct xnn_qs8_cvt_params) == 12, "parameter layout");
_Static_assert(__builtin_offsetof(struct xnn_qs8_cvt_params, scalar.input_zero_point) == 0,
               "input zero offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_cvt_params, scalar.multiplier) == 4,
               "multiplier offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_cvt_params, scalar.output_zero_point) == 8,
               "output zero offset");
#if defined(__riscv)
_Static_assert(__RISCV_VXRM_RNU == 0 && __RISCV_VXRM_RDN == 2, "rounding modes");
#endif
