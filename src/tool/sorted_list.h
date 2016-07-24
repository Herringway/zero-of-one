#ifndef _ZoO_TOOL_SORTED_LIST_H_
#define _ZoO_TOOL_SORTED_LIST_H_

#include <stdlib.h>

#include "../pervasive.h"

int ZoO_sorted_list_index_of
(
   ZoO_index const list_length,
   const void * const sorted_list,
   const void * const elem,
   size_t const type_size,
   int (*compare) (const void *, const void *, const void *),
   const void * const other,
   ZoO_index result [const restrict static 1]
);

#endif
