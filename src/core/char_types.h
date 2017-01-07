#ifndef _ZoO_CORE_CHAR_TYPES_H_
#define _ZoO_CORE_CHAR_TYPES_H_

enum ZoO_word_property
{
   ZoO_WORD_NO_PROPERTY,
   ZoO_WORD_HAS_NO_LEFT_SEPARATOR,
   ZoO_WORD_HAS_NO_RIGHT_SEPARATOR
};

/* ZoO_char = UTF-8 char */
typedef char ZoO_char;

/* Functions that can handle UTF-8 'char' will use this symbol. */
#define ZoO_CHAR_STRING_SYMBOL "%s"

#endif
