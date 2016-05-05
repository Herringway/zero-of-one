#ifndef _ZoO_TOOL_STRINGS_TYPES_H_
#define _ZoO_TOOL_STRINGS_TYPES_H_

#include <stdio.h>

#include "../pervasive.h"

struct ZoO_strings
{
   ZoO_index words_count;
   ZoO_char * restrict * restrict words;
   size_t * restrict word_sizes;
};

#endif
