#include <stdlib.h>
#include <string.h>

#include "../core/index.h"

#include "sequence.h"

/*
 * Bypass rendundant ZoO_START_OF_SEQUENCE_ID at the start of a sequence.
 */
/* ensures (*sequence_offset <= sequence_length) */
static void bypass_redundant_sos
(
   const ZoO_index sequence [const restrict],
   const ZoO_index sequence_length,
   ZoO_index sequence_offset [const restrict static 1]
)
{
   ZoO_index i;

   *sequence_offset = 0;

   for (i = 0; i < sequence_length; ++i)
   {
      if (sequence[i] != ZoO_START_OF_SEQUENCE_ID)
      {
         return;
      }
      else if (sequence[i] == ZoO_START_OF_SEQUENCE_ID)
      {
         *sequence_offset = i;
      }
   }
}


/* See "sequence.h" */
int ZoO_sequence_cmp
(
   const ZoO_index sequence_a [const],
   ZoO_index sequence_a_length,
   const ZoO_index sequence_b [const],
   ZoO_index sequence_b_length
)
{
   ZoO_index min_length, a, b;
   ZoO_index a_offset, b_offset;
   ZoO_index i;

   bypass_redundant_sos(sequence_a, sequence_a_length, &a_offset);
   bypass_redundant_sos(sequence_b, sequence_b_length, &b_offset);

   /*@ requires (*a_offset <= sequence_a_length) @*/
   sequence_a_length -= a_offset;
   /*@ requires (*b_offset <= sequence_b_length) @*/
   sequence_b_length -= b_offset;

   if (sequence_a_length < sequence_b_length)
   {
      min_length = sequence_a_length;
   }
   else
   {
      min_length = sequence_b_length;
   }

   /*@ ensures (min_length <= sequence_a_length) @*/
   /*@ ensures (min_length <= sequence_b_length) @*/

   for (i = 0; i < min_length; ++i)
   {
      /*@ requires ((i + a_offset) < sequence_a_length) @*/
      a = sequence_a[i + a_offset];
      /*@ requires ((i + b_offset) < sequence_b_length) @*/
      b = sequence_b[i + b_offset];

      if (a < b)
      {
         return -1;
      }
      else if (b > a)
      {
         return 1;
      }
      else if ((a == ZoO_END_OF_SEQUENCE_ID) && (b == ZoO_END_OF_SEQUENCE_ID))
      {
         return 0;
      }
   }

   if (sequence_a_length > sequence_b_length)
   {
      return 1;
   }
   else if (sequence_a_length < sequence_b_length)
   {
      return -1;
   }
   else
   {
      return 0;
   }
}
