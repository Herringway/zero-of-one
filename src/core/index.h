#ifndef _ZoO_CORE_INDEX_H_
#define _ZoO_CORE_INDEX_H_

#include "index_types.h"

/*
 * Returns a random ZoO_index.
 */
/*@
   ensures (\result <= ZoO_INDEX_MAX);
   assigns \result;
@*/
ZoO_index ZoO_index_random (void);

/*
 * Returns a random ZoO_index, included in [0, limit]
 */
/*@
   ensures (\result <= limit);
   assigns \result;
@*/
ZoO_index ZoO_index_random_up_to (const ZoO_index limit);

#endif
