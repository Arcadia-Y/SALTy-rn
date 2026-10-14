/* Fixed LP64 ABI and checked assertions; helpers have explicit Lean semantics. */
#define NULL ((void*)0)
#define XNN_OOB_READS
#define XNN_LIKELY(x) (x)
#define XNN_UNPREDICTABLE(x) (x)
extern void salty_assert(int);
#define assert(x) salty_assert(!!(x))
/* Same helper definitions as src/verification_bw/xnn_minimal.h. */
static inline size_t min(size_t a, size_t b) {
  return a < b ? a : b;
}
static inline size_t doz(size_t a, size_t b) {
  return a > b ? a - b : 0;
}
extern double floor(double);
struct xnn_qs8_rsum_params { char _; };
_Static_assert(sizeof(struct xnn_qs8_rsum_params) == 1, "dummy parameter layout");
