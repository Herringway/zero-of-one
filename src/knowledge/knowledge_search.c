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

/* pre: \length(sequence) >= markov_order */
int ZoO_knowledge_find_tws_targets
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence [restrict static 1],
   const ZoO_index markov_order, /* Pre: (> 0) */
   const ZoO_index * restrict targets [const restrict static 1],
   const ZoO_index * restrict targets_weights [const restrict static 1],
   ZoO_index targets_weights_sum [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   ZoO_index i, current_min, current_max, local_sequence;
   const ZoO_index * restrict candidate;
   const ZoO_index markov_sequence_length = (markov_order - 1);
   const ZoO_index word = sequence[0];

   if
   (
      (word >= k->words_length)
      || (k->words[word].occurrences == 0)
   )
   {
      ZoO_S_ERROR
      (
         io,
         "Attempting to find the TWS targets of an unknown word."
      );

      *targets = (const ZoO_index *) NULL;
      *targets_weights = (const ZoO_index *) NULL;
      *targets_weights_sum = 0;

      return -1;
   }


   if (markov_order == 1)
   {
      /* Special case: empty sequences. */
      *targets = (const ZoO_index *) k->words[word].tws.targets;

      *targets_weights =
         (const ZoO_index *) k->words[word].tws.targets_occurrences;

      *targets_weights_sum = k->words[word].occurrences;

      return 0;
   }


   /* pre: \length(sequence) >= markov_order */
   /* markov_order > 1 */
   sequence += 1; /* get the relevant part of the sequence. */

   /* Handles the case where the list is empty ********************************/
   current_max = k->words[word].tws.sequences_ref_length;

   if (current_max == 0)
   {
      *targets = (const ZoO_index *) NULL;
      *targets_weights = (const ZoO_index *) NULL;
      *targets_weights_sum = 0;

      ZoO_S_ERROR
      (
         io,
         "Attempting to find the TWS targets of a sequence that never had any."
      );

      return -2;
   }
   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   for (;;)
   {
      i = (current_min + ((current_max - current_min) / 2));

      local_sequence = k->words[word].tws.sequences_ref_sorted[i];

      (void) ZoO_knowledge_get_sequence
      (
         k,
         k->words[word].tws.sequences_ref[local_sequence],
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
            *targets = (const ZoO_index *) NULL;
            *targets_weights = (const ZoO_index *) NULL;
            *targets_weights_sum = 0;

            return -2;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min > current_max) || (i == 0))
         {
            *targets = (const ZoO_index *) NULL;
            *targets_weights = (const ZoO_index *) NULL;
            *targets_weights_sum = 0;

            return -2;
         }

         current_max = (i - 1);
      }
      else
      {
         *targets = k->words[word].tws.targets[local_sequence];

         *targets_weights =
            k->words[word].tws.targets_occurrences[local_sequence];

         *targets_weights_sum =
            k->words[word].tws.occurrences[local_sequence];

         return 0;
      }
   }
}

int ZoO_knowledge_find_swt_targets
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence [restrict static 1],
   const size_t sequence_length,
   const ZoO_index markov_order,
   const ZoO_index * restrict targets [const restrict static 1],
   const ZoO_index * restrict targets_weights [const restrict static 1],
   ZoO_index targets_weights_sum [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   ZoO_index i, current_min, current_max, local_sequence;
   const ZoO_index * restrict candidate;
   const ZoO_index markov_sequence_length = (markov_order - 1);
   const ZoO_index word = sequence[sequence_length - 1];

   if
   (
      (word >= k->words_length)
      || (k->words[word].occurrences == 0)
   )
   {
      ZoO_S_ERROR
      (
         io,
         "Attempting to find the SWT targets of an unknown word."
      );

      *targets = (const ZoO_index *) NULL;
      *targets_weights = (const ZoO_index *) NULL;
      *targets_weights_sum = 0;

      return -1;
   }

   if (markov_order == 1)
   {
      /* Special case: empty sequences. */
      *targets = (const ZoO_index *) k->words[word].swt.targets;

      *targets_weights =
         (const ZoO_index *) k->words[word].swt.targets_occurrences;

      *targets_weights_sum = k->words[word].occurrences;

      return 0;
   }

   sequence = (sequence + (sequence_length - markov_order));
   /* Handles the case where the list is empty ********************************/
   current_max = k->words[word].swt.sequences_ref_length;

   if (current_max == 0)
   {
      *targets = (const ZoO_index *) NULL;
      *targets_weights = (const ZoO_index *) NULL;
      *targets_weights_sum = 0;

      ZoO_S_WARNING
      (
         io,
         "Attempting to find the SWT targets of a sequence that never had any."
      );

      return -2;
   }
   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   for (;;)
   {
      i = (current_min + ((current_max - current_min) / 2));

      local_sequence = k->words[word].swt.sequences_ref_sorted[i];

      (void) ZoO_knowledge_get_sequence
      (
         k,
         k->words[word].swt.sequences_ref[local_sequence],
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
            *targets = (const ZoO_index *) NULL;
            *targets_weights = (const ZoO_index *) NULL;
            *targets_weights_sum = 0;

            return -2;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min > current_max) || (i == 0))
         {
            *targets = (const ZoO_index *) NULL;
            *targets_weights = (const ZoO_index *) NULL;
            *targets_weights_sum = 0;

            return -2;
         }

         current_max = (i - 1);
      }
      else
      {
         *targets = k->words[word].swt.targets[local_sequence];

         *targets_weights =
            k->words[word].swt.targets_occurrences[local_sequence];

         *targets_weights_sum =
            k->words[word].swt.occurrences[local_sequence];

         return 0;
      }
   }
}
