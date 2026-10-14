/* Fixed ABI and side-effect-free likelihood annotations. */
#define XNN_LIKELY(x) (x)
#define XNN_UNLIKELY(x) (x)
extern void salty_assert(int);
#define assert(x) salty_assert(!!(x))
