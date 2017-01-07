#include <stdlib.h>
#include <string.h>

#include "../core/index.h"

#include "sequence.h"

/* See "sequence.h" */
int ZoO_sequence_cmp
(
   const ZoO_index sequence_a [const],
   const ZoO_index sequence_a_length,
   const ZoO_index sequence_b [const],
   const ZoO_index sequence_b_length
)
{
   ZoO_index min_length;
   ZoO_index i;

   if (sequence_a_length < sequence_b_length)
   {
      min_length = sequence_a_length;
   }
   else
   {
      min_length = sequence_b_length;
   }

   for (i = 0; i < min_length; ++i)
   {
      if (sequence_a[i] < sequence_b[i])
      {
         return -1;
      }
      else if (sequence_b[i] > sequence_b[i])
      {
         return 1;
      }
      else if
      (
         (sequence_a[i] == ZoO_END_OF_SEQUENCE_ID)
         && (sequence_b[i] == ZoO_END_OF_SEQUENCE_ID)
      )
      {
         return 0;
      }
   }

   if (sequence_a_length < sequence_b_length)
   {
      if (sequence_b[i] == ZoO_END_OF_SEQUENCE_ID)
      {
         return 0;
      }
      else
      {
         return -1;
      }
   }
   else if (sequence_a_length > sequence_b_length)
   {
      if (sequence_a[i] == ZoO_END_OF_SEQUENCE_ID)
      {
         return 0;
      }
      else
      {
         return 1;
      }
   }
   else
   {
      return 0;
   }
}
