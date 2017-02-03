#include <stdlib.h>

#include "../core/char.h"
#include "../core/index.h"
#include "../sequence/sequence.h"

#include "../pipe/pipe.h"

#include "knowledge.h"

static int weighted_random_pick
(
   const struct ZoO_knowledge_sequence_data sd [const restrict static 1],
   ZoO_index result [const restrict static 1]
)
{
   ZoO_index accumulator, random_number;

   accumulator = 0;

   if (sd->occurrences == 0)
   {
      return -1;
   }

   random_number = ZoO_index_random_up_to(sd->occurrences);
   /*@ ensures (0 <= random_number <= weights_sum); @*/

   *result = 0;

   for (;;)
   {
      accumulator += sd->targets[*result].occurrences;

      if (accumulator < random_number)
      {
         *result += 1;
      }
      else
      {
         *result = sd->targets[*result].id;

         return 0;
      }
   }
}

int ZoO_knowledge_random_tws_target
(
   const struct ZoO_knowledge k [const static 1],
   ZoO_index target [const restrict static 1],
   const ZoO_index word_id,
   const ZoO_index sequence_id
)
{
   ZoO_index s_index;

   if
   (
      ZoO_knowledge_find_markov_sequence
      (
         sequence_id,
         &(k->words[word_id].tws),
         &s_index
      ) < 0
   )
   {
      return -1;
   }

   return
      weighted_random_pick
      (
         &(k->words[word_id].tws.sequences_ref[s_index]),
         target
      );
}

int ZoO_knowledge_random_swt_target
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence_id,
   const ZoO_index word_id,
   ZoO_index target [const restrict static 1]
)
{
   ZoO_index s_index;

   if
   (
      ZoO_knowledge_find_markov_sequence
      (
         sequence_id,
         &(k->words[word_id].swt),
         &s_index
      ) < 0
   )
   {
      return -1;
   }

   return
      weighted_random_pick
      (
         &(k->words[word_id].swt.sequences_ref[s_index]),
         target
      );
}
