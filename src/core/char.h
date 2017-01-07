#ifndef _ZoO_CORE_CHAR_H_
#define _ZoO_CORE_CHAR_H_

#include "char_types.h"

enum ZoO_word_property ZoO_get_word_property
(
   const ZoO_char word [const restrict],
   size_t word_size
);

int ZoO_word_cmp
(
   const ZoO_char word_a [const static 1],
   const ZoO_char word_b [const static 1]
);

int ZoO_char_is_punctuation (const ZoO_char c);
int ZoO_word_char_is_banned (const ZoO_char c);

#endif
