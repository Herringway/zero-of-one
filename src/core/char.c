#include <string.h>

#include "char.h"

/* See: "char.c" */
ZoO_char ZoO_char_to_lowercase (const ZoO_char c)
{
   if ((c >= 'A') && (c <= 'Z'))
   {
      return 'z' - ('Z' - c);
   }

   return c;
}

/* See: "char.c" */
int ZoO_word_cmp
(
   const ZoO_char word_a [const static 1],
   const size_t word_a_size,
   const ZoO_char word_b [const static 1],
   const size_t word_b_size
)
{
   int result;
   size_t min_size;

   if (word_a_size < word_b_size)
   {
      result =
         strncmp((const char *) word_a, (const char *) word_b, word_a_size);

      return (result == 0) ? -1 : result;
   }
   else if (word_b_size < word_a_size)
   {
      result =
         strncmp((const char *) word_a, (const char *) word_b, word_b_size);

      return (result == 0) ? 1 : result;
   }
   else
   {
      return strncmp((const char *) word_a, (const char *) word_b, word_a_size);
   }
}

