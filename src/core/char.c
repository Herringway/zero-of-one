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
int ZoO_char_is_banned (const ZoO_char c)
{
   switch (c)
   {
      case '(':
      case ')':
      case '[':
      case ']':
      case '{':
      case '}':
      case '<':
      case '>':
         return 1;

      default:
         return 0;
   }
}

/* See: "char.c" */
int ZoO_char_is_punctuation (const ZoO_char c)
{
   switch (c)
   {
      case '!':
      case ',':
      case '.':
      case ':':
      case ';':
      case '?':
         return 1;

      default:
         return 0;
   }
}

/* See: "char.c" */
int ZoO_word_cmp
(
   const ZoO_char word_a [const static 1],
   const size_t word_a_size,
   const ZoO_char word_b [const static 1]
)
{
   return strncmp((const char *) word_a, (const char *) word_b, word_a_size);
}

