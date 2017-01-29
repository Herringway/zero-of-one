#ifndef _ZoO_CORE_INDEX_TYPES_H_
#define _ZoO_CORE_INDEX_TYPES_H_

/*
 * ZoO_index is a replacement for size_t. As many indices are stored for every
 * word learned, having control over which type of variable is used to represent
 * those indices lets us scale the RAM usage.
 */

#include <limits.h>

/* Must be unsigned. */
typedef unsigned int ZoO_index;

/* Must be > 0. */
#define ZoO_INDEX_MAX UINT_MAX


#if (ZoO_INDEX_MAX > SIZE_MAX)
   #error "ZoO_index should not be able to go higher than a size_t variable."
#endif

#endif
