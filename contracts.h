/* Debugging with contracts; simulating cc0 -d
 * Automatically enabled, disable with gcc -DNDEBUG ...
 *
 * 15-122 Principles of Imperative Computation
 * Frank Pfenning
 *
 * (mbryant) 23 Mar 2014 - changed compilation method
 */

#include <assert.h>

/* Unlike typical header files, "contracts.h" may be
 * included multiple times, with and without NDEBUG defined.
 */

#ifndef NDEBUG

#define ASSERT(COND) assert(COND)
#define REQUIRES(COND) assert(COND)
#define ENSURES(COND) assert(COND)

#else

#define ASSERT(COND)
#define REQUIRES(COND)
#define ENSURES(COND)

#endif
