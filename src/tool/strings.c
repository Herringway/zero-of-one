#define _POSIX_C_SOURCE 200809L
#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../io/error.h"

#include "strings.h"


void ZoO_strings_initialize (struct ZoO_strings s [const restrict static 1])
{
   s->words_count = 0;
   s->words = (ZoO_char **) NULL;
   s->word_sizes = (size_t *) NULL;
}

void ZoO_strings_finalize (struct ZoO_strings s [const restrict static 1])
{
   if (s->words_count != 0)
   {
      ZoO_index i;

      for (i = 0; i < s->words_count; ++i)
      {
         free((void *) s->words[i]);
      }

      s->words_count = 0;

      free((void *) s->words);
      free((void *) s->word_sizes);

      s->words = (ZoO_char **) NULL;
      s->word_sizes = (size_t *) NULL;
   }
}

static int add_word
(
   struct ZoO_strings s [const restrict static 1],
   size_t const line_size,
   const ZoO_char line [const restrict static line_size]
)
{
   size_t * new_s_word_sizes;
   ZoO_char * new_word, ** new_s_words;

   if (s->words_count == ZoO_INDEX_MAX)
   {
      ZoO_S_WARNING("Data input sentence has too many words.");

      return -1;
   }

   /* overflow-safe, as line_size < SIZE_MAX */
   new_word = (ZoO_char *) calloc((line_size + 1), sizeof(ZoO_char));

   if (new_word == (ZoO_char *) NULL)
   {
      ZoO_S_WARNING("Unable to allocate memory to extract new word.");

      return -1;
   }

   memcpy((void *) new_word, (const void *) line, line_size);

   new_word[line_size] = '\0';

   new_s_words =
      (ZoO_char **) realloc
      (
         (void *) s->words,
         /* XXX: (sizeof() * _) assumed overflow-safe. */
         /* (di->words_count + 1) overflow-safe */
         (sizeof(ZoO_char *) * (s->words_count + 1))
      );

   if (new_s_words == (ZoO_char **) NULL)
   {
      ZoO_S_WARNING("Unable to reallocate memory to extract new word.");

      free((void *) new_word);

      return -1;
   }

   s->words = new_s_words;

   new_s_word_sizes =
      (size_t *) realloc
      (
         (void *) s->word_sizes,
         /* XXX: (sizeof() * _) assumed overflow-safe. */
         /* (di->words_count + 1) overflow-safe */
         (sizeof(size_t) * (s->words_count + 1))
      );

   if (new_s_word_sizes == (size_t *) NULL)
   {
      ZoO_S_WARNING("Unable to reallocate memory to extract new word.");

      free((void *) new_word);

      return -1;
   }

   s->word_sizes = new_s_word_sizes;

   s->words[s->words_count] = new_word;
   s->word_sizes[s->words_count] = (line_size + 1);

   s->words_count += 1;

   return 0;
}

static int parse_word
(
   struct ZoO_strings s [const restrict static 1],
   ZoO_index const punctuations_count,
   const ZoO_char punctuations [const restrict static punctuations_count],
   size_t const line_size,
   ZoO_char line [const static line_size]
)
{
   ZoO_index j;

   if (line_size == 0)
   {
      return 0;
   }

   for (j = 0; j < line_size; ++j)
   {
      switch (line[j])
      {
         case 'A':
         case 'B':
         case 'C':
         case 'D':
         case 'E':
         case 'F':
         case 'G':
         case 'H':
         case 'I':
         case 'J':
         case 'K':
         case 'L':
         case 'M':
         case 'N':
         case 'O':
         case 'P':
         case 'Q':
         case 'R':
         case 'S':
         case 'T':
         case 'U':
         case 'V':
         case 'W':
         case 'X':
         case 'Y':
         case 'Z':
            line[j] = 'z' - ('Z' - line[j]);
            break;

         default:
            break;
      }
   }

   for (j = 0; j < punctuations_count; ++j)
   {
      /* overflow-safe: line_size > 1 */
      if (line[line_size - 1] == punctuations[j])
      {
         if (line_size > 1)
         {
            if
            (
               /* overflow-safe: line_size > 1 */
               (add_word(s, (line_size - 1), line) < 0)
               /* overflow-safe: line_size > 1 */
               /* prevents line[restrict] */
               || (add_word(s, 1, (line + (line_size - 1))) < 0)
            )
            {
               return -1;
            }

            return 0;
         }
      }
   }

   return add_word(s, line_size, line);
}

int ZoO_strings_parse
(
   struct ZoO_strings s [const restrict static 1],
   size_t const input_size,
   ZoO_char input [const restrict],
   ZoO_index const punctuations_count,
   const ZoO_char punctuations [const restrict static punctuations_count]
)
{
   size_t i, w_start;

   ZoO_strings_finalize(s);

   if (input == NULL)
   {
      return 0;
   }

   i = 0;

   /* overflow-safe: input is '\0' terminated. */
   while (input[i] == ' ')
   {
      ++i;
   }

   w_start = i;

   for (; i < input_size; ++i)
   {
      if (input[i] == ' ')
      {
         if
         (
            parse_word
            (
               s,
               punctuations_count,
               punctuations,
               /* overflow-safe: w_start < i */
               (i - w_start),
               (input + w_start)
            ) < 0
         )
         {
            ZoO_strings_finalize(s);

            return -1;
         }

         ++i;

         /* safe, as input is terminated by '\0' */
         while (input[i] == ' ')
         {
            ++i;
         }

         w_start = i;
      }
   }

   if
   (
      parse_word
      (
         s,
         punctuations_count,
         punctuations,
         /* overflow-safe: w_start < i */
         (i - w_start),
         (input + w_start)
      ) < 0
   )
   {
      ZoO_strings_finalize(s);

      return -1;
   }

   return 0;
}
