#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/sequence.h"

#include "../pipe/pipe.h"

#include "knowledge.h"

/******************************************************************************/
/** LEARN FOLLOWING SEQUENCE **************************************************/
/******************************************************************************/
static int add_following_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index index,
   const ZoO_index sequence_length,
   const ZoO_index markov_order,
   const struct ZoO_pipe io [const restrict static 1]
);

/******************************************************************************/
/** LEARN PRECEDING SEQUENCE **************************************************/
/******************************************************************************/
static int add_preceding_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index index,
   const ZoO_index sequence_length,
   const ZoO_index markov_order,
   const struct ZoO_pipe io [const restrict static 1]
)
{
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

int ZoO_knowledge_learn_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index sequence_length,
   const ZoO_index markov_order,
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index * buffer;
   ZoO_index i;
   const ZoO_index buffer_length = (markov_order - 1);

   /* TODO */

   for (i = 0; i < sequence_length; ++i)
   {
      k->words[sequence[i]].occurrences += 1;

      add_preceding_sequence
      (
         k,
         sequence,
         i,
         sequence_length,
         buffer_length,
         io
      );

      add_following_sequence
      (
         k,
         sequence,
         i,
         sequence_length,
         markov_order,
         io
      );

      /*
       * TODO: in case of failure, undo part of the word done so far: instead
       * of unlearning, just remove the occurrence count of sequences and
       * words so that {k} remains coherent.
       */
   }

   return 0;
}
