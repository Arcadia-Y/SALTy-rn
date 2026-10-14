/* Fixed AArch64 source branch and LP64 ABI. Assertions remain checked. */
#define NULL ((void*)0)
#define XNN_OOB_READS
#define XNN_UNLIKELY(x) (x)
#define XNN_ALIGN(n) __attribute__((aligned(n)))
#define XNN_ARCH_ARM64 1
extern void salty_assert(int);
#define assert(x) salty_assert(!!(x))
struct xnn_qs8_rsum_params { char _; };
_Static_assert(sizeof(struct xnn_qs8_rsum_params) == 1, "dummy parameter layout");
