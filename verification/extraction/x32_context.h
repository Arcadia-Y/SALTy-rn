/* Fixed source ABI/helper context. Model declarations keep helper calls named;
 * real compilation uses these exact definitions, matching xnn_minimal.h. */
#define XNN_OOB_READS
#define XNN_UNPREDICTABLE(x) (x)
extern void salty_assert(int);
#define assert(x) salty_assert(!!(x))
#ifndef SALTY_MODEL_INTERFACE
static inline size_t round_down_po2(size_t n, size_t q) { return n & -q; }
static inline size_t doz(size_t a, size_t b) { return a > b ? a - b : 0; }
#endif
