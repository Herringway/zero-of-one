#include <stdlib.h>
#include <string.h>

#include "../core/index.h"

#include "sequence.h"

/* See "sequence.h" */
/*@
   requires
   (
      \valid(sequence_a+ (0 .. sequence_a_length))
      || (sequence_a_length == 0)
   );

   requires
   (
      \valid(sequence_b+ (0 .. sequence_b_length))
      || (sequence_b_length == 0)
   );

   assigns \result;
@*/
int ZoO_sequence_cmp
(
   const ZoO_index sequence_a [const restrict static 1],
   const ZoO_index sequence_b [const restrict static 1],
   const ZoO_index length
)
{
   ZoO_index i, a, b;

   for (i = 0; i < length; ++i)
   {
      a = sequence_a[i];
      b = sequence_b[i];

      if (a < b)
      {
         return -1;
      }
      else if (a > b)
      {
         return 1;
      }
   }

   return 0;
}

