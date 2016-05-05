#ifndef _ZoO_TOOL_STRINGS_H_
#define _ZoO_TOOL_STRINGS_H_

#include "strings_types.h"

void ZoO_strings_initialize (struct ZoO_strings s [const restrict static 1]);

void ZoO_strings_finalize (struct ZoO_strings s [const restrict static 1]);

int ZoO_strings_parse
(
   struct ZoO_strings s [const static 1],
   size_t const input_size,
   ZoO_char input [const restrict],
   ZoO_index const punctuations_count,
   const ZoO_char punctuations [const restrict static punctuations_count]
);

#endif
