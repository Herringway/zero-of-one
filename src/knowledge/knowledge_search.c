#include <stdlib.h>

#include "../core/char.h"
#include "../core/index.h"
#include "../sequence/sequence.h"

#include "../pipe/pipe.h"

#include "knowledge.h"

/* See "knowledge.h". */
int ZoO_knowledge_find_word_id
(
   const struct ZoO_knowledge k [const restrict static 1],
   const ZoO_char word [const restrict static 1],
   const size_t word_length,
   ZoO_index result [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   ZoO_index i, current_min, current_max;
   ZoO_index candidate_id;

   /* Handles the case where the list is empty ********************************/
   current_max = k->words_length;

   if (current_max == 0)
   {
      *result = 0;

      return -1;
   }
   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   for (;;)
   {
      i = (current_min + ((current_max - current_min) / 2));

      cmp = ZoO_word_cmp(word, word_length, k->words[k->words_sorted[i]].word);

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *result = current_min;

            return -1;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min > current_max) || (i == 0))
         {
            *result = current_min;

            return -1;
         }

         current_max = (i - 1);
      }
      else
      {
         *result = k->words_sorted[i];

         return 0;
      }
   }
}

int ZoO_knowledge_find_preceding_words
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence [const restrict],
   const ZoO_index markov_order, /* Pre: (> 0) */
   const ZoO_index * restrict preceding_words [const restrict static 1],
   const ZoO_index * restrict preceding_words_weights [const restrict static 1],
   ZoO_index preceding_words_weights_sum [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   ZoO_index i, current_min, current_max, local_sequence;
   const ZoO_index * restrict candidate;
   const ZoO_index markov_sequence_length = (markov_order - 1);
   const ZoO_index word = sequence[markov_sequence_length];

   if (word >= k->words_length)
   {
      ZoO_S_ERROR
      (
         io,
         "Attempting to find the preceding words of an unknown word."
      );

      *preceding_words = (const ZoO_index *) NULL;
      *preceding_words_weights = (const ZoO_index *) NULL;
      *preceding_words_weights_sum = 0;

      return -1;
   }


   if (markov_order == 1)
   {
      /* Special case: empty sequences. */
      *preceding_words = (const ZoO_index *) k->words[word].preceded.targets;

      *preceding_words_weights =
         (const ZoO_index *) k->words[word].preceded.targets_occurrences;

      *preceding_words_weights_sum = k->words[word].occurrences;

      return 0;
   }

   /* Handles the case where the list is empty ********************************/
   current_max = k->words[word].preceded.sequences_ref_length;

   if (current_max == 0)
   {
      *preceding_words = (const ZoO_index *) NULL;
      *preceding_words_weights = (const ZoO_index *) NULL;
      *preceding_words_weights_sum = 0;

      ZoO_S_ERROR
      (
         io,
         "Attempting to find the preceding words of a sequence that never had "
         "any."
      );

      return -2;
   }
   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   for (;;)
   {
      i = (current_min + ((current_max - current_min) / 2));

      local_sequence = k->words[word].preceded.sequences_ref_sorted[i];

      (void) ZoO_knowledge_get_sequence
      (
         k,
         k->words[word].preceded.sequences_ref[local_sequence],
         &candidate,
         io
      );

      cmp =
         ZoO_sequence_cmp
         (
            sequence,
            markov_sequence_length,
            candidate,
            markov_sequence_length
         );

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *preceding_words = (const ZoO_index *) NULL;
            *preceding_words_weights = (const ZoO_index *) NULL;
            *preceding_words_weights_sum = 0;

            return -2;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min > current_max) || (i == 0))
         {
            *preceding_words = (const ZoO_index *) NULL;
            *preceding_words_weights = (const ZoO_index *) NULL;
            *preceding_words_weights_sum = 0;

            return -2;
         }

         current_max = (i - 1);
      }
      else
      {
         *preceding_words = k->words[word].preceded.targets[local_sequence];

         *preceding_words_weights =
            k->words[word].preceded.targets_occurrences[local_sequence];

         *preceding_words_weights_sum =
            k->words[word].preceded.occurrences[local_sequence];

         return 0;
      }
   }
}

int ZoO_knowledge_find_following_words
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence [const restrict],
   const size_t sequence_length,
   const ZoO_index markov_order,
   const ZoO_index * restrict following_words [const restrict static 1],
   const ZoO_index * restrict following_words_weights [const restrict static 1],
   ZoO_index following_words_weights_sum [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   ZoO_index i, current_min, current_max, local_sequence;
   const ZoO_index * restrict candidate;
   const ZoO_index markov_sequence_length = (markov_order - 1);
   const size_t sequence_offset =
      ((sequence_length - ((size_t) markov_sequence_length)) - 1);
   const ZoO_index word = sequence[sequence_offset];

   if (word >= k->words_length)
   {
      ZoO_S_ERROR
      (
         io,
         "Attempting to find the following words of an unknown word."
      );

      *following_words = (const ZoO_index *) NULL;
      *following_words_weights = (const ZoO_index *) NULL;
      *following_words_weights_sum = 0;

      return -1;
   }

   if (markov_order == 1)
   {
      /* Special case: empty sequences. */
      *following_words = (const ZoO_index *) k->words[word].preceded.targets;

      *following_words_weights =
         (const ZoO_index *) k->words[word].preceded.targets_occurrences;

      *following_words_weights_sum = k->words[word].occurrences;

      return 0;
   }

   /* Handles the case where the list is empty ********************************/
   current_max = k->words[word].preceded.sequences_ref_length;

   if (current_max == 0)
   {
      *following_words = (const ZoO_index *) NULL;
      *following_words_weights = (const ZoO_index *) NULL;
      *following_words_weights_sum = 0;

      ZoO_S_WARNING
      (
         io,
         "Attempting to find the following words of a sequence that never had "
         "any."
      );

      return -2;
   }
   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   for (;;)
   {
      i = (current_min + ((current_max - current_min) / 2));

      local_sequence = k->words[word].followed.sequences_ref_sorted[i];

      (void) ZoO_knowledge_get_sequence
      (
         k,
         k->words[word].followed.sequences_ref[local_sequence],
         &candidate,
         io
      );

      cmp =
         ZoO_sequence_cmp
         (
            (sequence + sequence_offset),
            markov_sequence_length,
            candidate,
            markov_sequence_length
         );

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *following_words = (const ZoO_index *) NULL;
            *following_words_weights = (const ZoO_index *) NULL;
            *following_words_weights_sum = 0;

            return -2;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min > current_max) || (i == 0))
         {
            *following_words = (const ZoO_index *) NULL;
            *following_words_weights = (const ZoO_index *) NULL;
            *following_words_weights_sum = 0;

            return -2;
         }

         current_max = (i - 1);
      }
      else
      {
         *following_words = k->words[word].followed.targets[local_sequence];

         *following_words_weights =
            k->words[word].followed.targets_occurrences[local_sequence];

         *following_words_weights_sum =
            k->words[word].followed.occurrences[local_sequence];

         return 0;
      }
   }
}
