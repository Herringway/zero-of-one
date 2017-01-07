#include <string.h>

#include "char.h"

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

int ZoO_word_cmp
(
   const ZoO_char word_a [const static 1],
   const ZoO_char word_b [const static 1]
)
{
   return strcmp((const char *) word_a, (const char *) word_b);
}
