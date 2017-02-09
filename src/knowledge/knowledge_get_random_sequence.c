#include <stdlib.h>

#include "../core/char.h"
#include "../core/index.h"

#include "../sequence/sequence.h"

#include "../error/error.h"

#include "knowledge.h"

static int weighted_random_pick
(
   const struct ZoO_knowledge_sequence_collection sc [const restrict static 1],
   const ZoO_index sum,
   ZoO_index result [const restrict static 1]
)
{
   ZoO_index accumulator, random_number;

   accumulator = 0;

   if (sum == 0)
   {
      return -1;
   }

   random_number = ZoO_index_random_up_to(sum);
   /*@ ensures (0 <= random_number <= weights_sum); @*/

   *result = 0;

   for (;;)
   {
      accumulator += sc->sequences_ref[*result].occurrences;

      if (accumulator < random_number)
      {
         *result += 1;
      }
      else
      {
         *result = sc->sequences_ref[*result].id;

         return 0;
      }
   }
}

int ZoO_knowledge_copy_random_swt_sequence
(
   const struct ZoO_knowledge k [const static 1],
   ZoO_index sequence [const restrict static 1],
   const ZoO_index word_id,
   const ZoO_index markov_order,
   FILE io [const restrict static 1]
)
{
   ZoO_index sequence_id;

   if
   (
      weighted_random_pick
      (
         &(k->words[word_id].swt),
         k->words[word_id].occurrences,
         &sequence_id
      ) < 0
   )
   {
      /* TODO: Err message. */

      return -1;
   }

   memcpy
   (
      (void *) sequence,
      (const void *) k->sequences[sequence_id],
      (((size_t) (markov_order - 1)) * sizeof(ZoO_index))
   );

   return 0;
}
