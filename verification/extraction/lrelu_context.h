/* Fixed LP64 context; assertions remain checked model operations. */
#define NULL ((void*)0)
#define XNN_OOB_READS
#define XNN_UNLIKELY(x) (x)
extern void salty_assert(int);
#define assert(x) salty_assert(!!(x))
struct xnn_qs8_lrelu_params {
  struct {
    int32_t input_zero_point;
    int32_t positive_multiplier;
    int32_t negative_multiplier;
    int32_t output_zero_point;
  } scalar;
};
_Static_assert(sizeof(struct xnn_qs8_lrelu_params) == 16, "parameter layout");
_Static_assert(__builtin_offsetof(struct xnn_qs8_lrelu_params, scalar.input_zero_point) == 0,
               "input zero offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_lrelu_params, scalar.positive_multiplier) == 4,
               "positive multiplier offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_lrelu_params, scalar.negative_multiplier) == 8,
               "negative multiplier offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_lrelu_params, scalar.output_zero_point) == 12,
               "output zero offset");
#if defined(__riscv)
_Static_assert(__RISCV_VXRM_RNU == 0 && __RISCV_VXRM_RDN == 2, "rounding modes");
#endif
