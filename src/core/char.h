#ifndef _ZoO_CORE_CHAR_H_
#define _ZoO_CORE_CHAR_H_

#include "char_types.h"

/* Compares two words. {word_a} does not have to be null terminated. */
/*@
 @ requires null_terminated_string(word_b);
 @ requires ((length(word_a) * sizeof(ZoO_char)) == word_a_size);
 @ ensures ((\result == 1) || (\result == 0) || (\result == -1));
 @*/
int ZoO_word_cmp
(
   const ZoO_char word_a [const static 1],
   const size_t word_a_size,
   const ZoO_char word_b [const static 1],
   const size_t word_b_size
);

/*
 * Returns the lowercase equivalent of ZoO_char that are included in ['A','Z'].
 * Other ZoO_char are returned untouched.
 */
ZoO_char ZoO_char_to_lowercase (const ZoO_char c);

#endif

