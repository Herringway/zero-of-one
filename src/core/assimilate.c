#include <stdlib.h>
#include <string.h>

#include "../io/error.h"

#include "knowledge.h"

static int link_to
(
   ZoO_index links_count [const restrict static 1],
   ZoO_index * links_occurrences [const restrict static 1],
   ZoO_index * links [const restrict static 1],
   ZoO_index const target
)
{
   ZoO_index i, * new_p;

   for (i = 0; i < *links_count; ++i)
   {
      if ((*links)[i] == target)
      {
         if ((*links_occurrences)[i] == ZoO_INDEX_MAX)
         {
            ZoO_S_WARNING
            (
               "Maximum link occurrences count has been reached."
            );

            return -1;
         }

         (*links_occurrences)[i] += 1;

         return 0;
      }
   }

   if (*links_count == ZoO_INDEX_MAX)
   {
      ZoO_S_WARNING("Maximum links count has been reached.");

      return -1;
   }

   new_p =
      (ZoO_index *) realloc
      (
         *links_occurrences,
         (
            (
               /* Safe: *links_count < ZoO_INDEX_MAX */
               (size_t) (*links_count + 1)
            )
            * sizeof(ZoO_index)
         )
      );

   if (new_p == (ZoO_index *) NULL)
   {
      ZoO_S_ERROR("Could not reallocate a link occurrences list.");

      return -1;
   }

   new_p[*links_count] = 1;

   *links_occurrences = new_p;

   new_p =
      (ZoO_index *) realloc
      (
         *links,
         (
            (
               /* Safe: *links_count < ZoO_INDEX_MAX */
               (size_t) (*links_count + 1)
            ) * sizeof(ZoO_index)
         )
      );

   if (new_p == (ZoO_index *) NULL)
   {
      ZoO_S_ERROR("Could not reallocate a link list.");

      return -1;
   }

   new_p[*links_count] = target;

   *links = new_p;

   *links_count += 1;

   return 0;
}

static int link_words
(
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_index const a,
   ZoO_index const b
)
{
   int error;

   error =
      link_to
      (
         &(k->words[a].forward_links_count),
         &(k->words[a].forward_links_occurrences),
         &(k->words[a].forward_links),
         b
      );

   error =
      (
         link_to
         (
            &(k->words[b].backward_links_count),
            &(k->words[b].backward_links_occurrences),
            &(k->words[b].backward_links),
            a
         )
         | error
      );

   return error;
}

int ZoO_knowledge_assimilate
(
   struct ZoO_knowledge k [const static 1],
   struct ZoO_strings string [const restrict static 1],
   ZoO_index const aliases_count,
   const char * restrict aliases [const restrict static aliases_count]
)
{
   int error;
   ZoO_index curr_word, next_word;
   ZoO_index curr_word_id, next_word_id;

   curr_word = 0;

   if (string->words_count == 0)
   {
      return 0;
   }

   for (curr_word = 0; curr_word < aliases_count; ++curr_word)
   {
      if (ZoO_IS_PREFIX(aliases[curr_word], string->words[0]))
      {
         return 0;
      }
   }

   curr_word = 0;

   if (ZoO_knowledge_learn(k, string->words[curr_word], &curr_word_id) < 0)
   {
      return -1;
   }

   if (link_words(k, ZoO_WORD_START_OF_LINE, curr_word_id) < 0)
   {
      error = -1;

      ZoO_WARNING
      (
         "Could not indicate that '"
         ZoO_CHAR_STRING_SYMBOL
         "' was the first word of the sentence.",
         string->words[0]
      );
   }

   next_word = 1;

   error = 0;

   while (next_word < string->words_count)
   {
      /* prevents words [restrict], k [restrict] */
      if (ZoO_knowledge_learn(k, string->words[next_word], &next_word_id) < 0)
      {
         return -1;
      }

      if (link_words(k, curr_word_id, next_word_id) < 0)
      {
         error = -1;

         ZoO_WARNING
         (
            "Could not add a link between words '"
            ZoO_CHAR_STRING_SYMBOL
            "' and '"
            ZoO_CHAR_STRING_SYMBOL
            "'.",
            string->words[curr_word],
            string->words[next_word]
         );
      }

      curr_word = next_word;
      curr_word_id = next_word_id;
      /*
       * Safe:
       *  - next_word < words_count
       *  - words_count =< ZoO_INDEX_MAX
       *  ----
       *  next_word < ZoO_INDEX_MAX
       */
      next_word += 1;
   }

   if (link_words(k, curr_word_id, ZoO_WORD_END_OF_LINE) < 0)
   {
      error = -1;

      ZoO_WARNING
      (
         "Could not indicate that '"
         ZoO_CHAR_STRING_SYMBOL
         "' was the last word of the sentence.",
         string->words[curr_word_id]
      );
   }

   return error;
}

