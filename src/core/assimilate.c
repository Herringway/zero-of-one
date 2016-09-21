#include <stdlib.h>
#include <string.h>

#include "../io/error.h"

#include "knowledge.h"

/** Functions to assimilate sentences using a ZoO_knowledge structure *********/


static int add_sequence
(
   ZoO_index links_count [const],
   struct ZoO_knowledge_link * links [const],
   ZoO_index const sequence [const restrict static ZoO_MARKOV_ORDER],
   ZoO_index const target_i,
   ZoO_index const offset
)
{
   ZoO_index link_index, i;
   struct ZoO_knowledge_link * link;
   ZoO_index * new_p;

   if
   (
      ZoO_knowledge_get_link
      (
         links_count,
         links,
         (sequence + offset),
         &link_index
      ) < 0
   )
   {
      return -1;
   }

   link = (*links + link_index);
   link->occurrences += 1;

   for (i = 0; i < link->targets_count; ++i)
   {
      if (link->targets[i] == sequence[target_i])
      {
         link->targets_occurrences[i] += 1;

         return 0;
      }
   }

   link->targets_count += 1;

   new_p =
      (ZoO_index *) realloc
      (
         (void *) link->targets,
         (sizeof(ZoO_index) * link->targets_count)
      );

   if (new_p == (ZoO_index *) NULL)
   {
      link->targets_count -= 1;

      /* TODO: err. */
      return -1;
   }

   link->targets = new_p;
   link->targets[link->targets_count - 1] = sequence[target_i];

   new_p =
      (ZoO_index *) realloc
      (
         (void *) link->targets_occurrences,
         (sizeof(ZoO_index) * link->targets_count)
      );

   if (new_p == (ZoO_index *) NULL)
   {
      link->targets_count -= 1;

      /* TODO: err. */
      return -1;
   }

   link->targets_occurrences = new_p;
   link->targets_occurrences[link->targets_count - 1] = 1;

   return 0;
}

static int add_word_occurrence
(
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_index const sequence [const static ((ZoO_MARKOV_ORDER * 2) + 1)]
)
{
   ZoO_index w;
   int error;

   w = sequence[ZoO_MARKOV_ORDER];

   error =
      add_sequence
      (
         &(k->words[w].forward_links_count),
         &(k->words[w].forward_links),
         sequence + (ZoO_MARKOV_ORDER + 1),
         (ZoO_MARKOV_ORDER - 1),
         0
      );

   error =
      (
         add_sequence
         (
            &(k->words[w].backward_links_count),
            &(k->words[w].backward_links),
            sequence,
            0,
            1
         )
         | error
      );

   return error;
}

static int should_assimilate
(
   struct ZoO_strings string [const restrict static 1],
   ZoO_index const aliases_count,
   const char * restrict aliases [const restrict static aliases_count]
)
{
   ZoO_index i;

   /* Don't assimilate empty strings. */
   if (string->words_count == 0)
   {
      return 0;
   }

   /* Don't assimilate things that start with our name. */
   for (i = 0; i < aliases_count; ++i)
   {
      if (ZoO_IS_PREFIX(aliases[i], string->words[0]))
      {
         return 0;
      }
   }

   return 1;
}

static int init_sequence
(
   struct ZoO_knowledge k [const static 1],
   struct ZoO_strings string [const restrict static 1],
   ZoO_index sequence [const restrict static ((ZoO_MARKOV_ORDER * 2) + 1)]
)
{
   ZoO_index i;

   /* We are going to link this sequence to ZoO_WORD_START_OF_LINE */
   sequence[ZoO_MARKOV_ORDER] = ZoO_WORD_START_OF_LINE;

   for (i = 1; i <= ZoO_MARKOV_ORDER; ++i)
   {
      sequence[ZoO_MARKOV_ORDER - i] = ZoO_WORD_START_OF_LINE;

      if (i <= string->words_count)
      {
         if
         (
            ZoO_knowledge_learn
            (
               k,
               string->words[i - 1],
               (sequence + (ZoO_MARKOV_ORDER + i))
            ) < 0
         )
         {
            return -1;
         }
      }
      else
      {
         sequence[ZoO_MARKOV_ORDER + i] = ZoO_WORD_END_OF_LINE;
      }
   }

   return 0;
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
   ZoO_index sequence[(ZoO_MARKOV_ORDER * 2) + 1];
   ZoO_index next_word, new_word, new_word_id;

   if (!should_assimilate(string, aliases_count, aliases))
   {
      return 0;
   }

   if (init_sequence(k, string, sequence) < 0)
   {
      return -1;
   }

   if (add_word_occurrence(k, sequence) < 0)
   {
      error = -1;

      /* There's a pun... */
      ZoO_S_WARNING("Could not add a link between words.");

      return -1;
   }

   error = 0;

   next_word = 0;
   new_word = ZoO_MARKOV_ORDER;

   while (next_word <= (string->words_count + ZoO_MARKOV_ORDER))
   {
      if (new_word < string->words_count)
      {
         /* prevents words [restrict], k [restrict] */
         if (ZoO_knowledge_learn(k, string->words[new_word], &new_word_id) < 0)
         {
            return -1;
         }
      }
      else
      {
         new_word_id = ZoO_WORD_END_OF_LINE;
      }

      memmove
      (
         (void *) sequence,
         (const void *) (sequence + 1),
         /* Accepts 0. */
         (sizeof(ZoO_index) * (ZoO_MARKOV_ORDER * 2))
      );

      sequence[ZoO_MARKOV_ORDER * 2] = new_word_id;

      if (add_word_occurrence(k, sequence) < 0)
      {
         error = -1;

         /* There's a pun... */
         ZoO_S_WARNING("Could not add a link between words.");

         return -1;
      }

      /*
       * Safe:
       *  - next_word < words_count
       *  - words_count =< ZoO_INDEX_MAX
       *  ----
       *  next_word < ZoO_INDEX_MAX
       */
      next_word += 1;
      new_word += 1;
   }

   return error;
}

