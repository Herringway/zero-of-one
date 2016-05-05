#ifndef _ZoO_CORE_KNOWLEDGE_H_
#define _ZoO_CORE_KNOWLEDGE_H_

#include "../tool/strings_types.h"

#include "knowledge_types.h"

int ZoO_knowledge_initialize (struct ZoO_knowledge k [const static 1]);

void ZoO_knowledge_finalize (struct ZoO_knowledge k [const static 1]);

int ZoO_knowledge_find
(
   const struct ZoO_knowledge k [const restrict static 1],
   const ZoO_char word [const restrict static 1],
   ZoO_index result [const restrict static 1]
);

int ZoO_knowledge_learn
(
   struct ZoO_knowledge k [const static 1],
   const ZoO_char word [const restrict static 1],
   ZoO_index result [const restrict static 1]
);

int ZoO_knowledge_assimilate
(
   struct ZoO_knowledge k [const static 1],
   struct ZoO_strings string [const restrict static 1],
   ZoO_index const aliases_count,
   const char * restrict aliases [const restrict static aliases_count]
);

int ZoO_knowledge_extend
(
   struct ZoO_knowledge k [const static 1],
   const struct ZoO_strings string [const static 1],
   int const ignore_first_word,
   ZoO_char * result [const static 1]
);

#endif
