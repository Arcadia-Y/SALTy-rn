/* Fixed compilation context. Assertions remain checked model operations. */
#define NULL ((void*)0)
#define XNN_OOB_READS
#define XNN_UNLIKELY(x) (x)
extern void salty_assert(int);
#define assert(x) salty_assert(!!(x))
struct xnn_s8_minmax_params {
  struct { int32_t min; int32_t max; } scalar;
};
_Static_assert(sizeof(struct xnn_s8_minmax_params) == 8, "parameter layout");
_Static_assert(__builtin_offsetof(struct xnn_s8_minmax_params, scalar.max) == 4,
               "parameter field offset");
