/* Fixed LP64 layout; checked assertions, no intrinsic implementations. */
#define NULL ((void*)0)
#define XNN_OOB_READS
#define XNN_UNLIKELY(x) (x)
#define XNN_LIKELY(x) (x)
extern void salty_assert(int);
#define assert(x) salty_assert(!!(x))
struct xnn_qs8_add_minmax_params {
  struct { int8_t a_zero_point,b_zero_point; int32_t bias,a_multiplier,b_multiplier,shift;
    int16_t output_zero_point; int8_t output_min,output_max; } scalar;
};
_Static_assert(sizeof(struct xnn_qs8_add_minmax_params) == 24, "parameter layout");
_Static_assert(__builtin_offsetof(struct xnn_qs8_add_minmax_params, scalar.a_zero_point) == 0, "a_zero_point offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_add_minmax_params, scalar.b_zero_point) == 1, "b_zero_point offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_add_minmax_params, scalar.bias) == 4, "bias offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_add_minmax_params, scalar.a_multiplier) == 8, "a_multiplier offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_add_minmax_params, scalar.b_multiplier) == 12, "b_multiplier offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_add_minmax_params, scalar.shift) == 16, "shift offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_add_minmax_params, scalar.output_zero_point) == 20, "output_zero_point offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_add_minmax_params, scalar.output_min) == 22, "output_min offset");
_Static_assert(__builtin_offsetof(struct xnn_qs8_add_minmax_params, scalar.output_max) == 23, "output_max offset");
#if defined(__riscv)
_Static_assert(__RISCV_VXRM_RNU == 0 && __RISCV_VXRM_RDN == 2, "rounding modes");
#endif
