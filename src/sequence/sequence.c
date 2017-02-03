#include <stdlib.h>
#include <string.h>

#include "../core/index.h"

#include "sequence.h"

/*
 * Bypass rendundant ZoO_START_OF_SEQUENCE_ID at the start of a sequence.
 */
/*@
   requires
   (
      \valid(sequence+ (0 .. sequence_length))
      || (sequence_length == 0)
   );
   requires \separated(sequence, sequence_offset);

   assigns (*sequence_offset);

   ensures (*sequence_offset < sequence_length);

   ensures
   (
      (*sequence_offset == 0)
      || (sequence[0 .. *sequence_offset] == ZoO_START_OF_SEQUENCE_ID)
   );

   ensures
   (
      (*sequence_offset == sequence_length)
      || (sequence[*sequence_offset + 1] != ZoO_START_OF_SEQUENCE_ID)
   );

@*/
static void bypass_redundant_sos
(
   const ZoO_index sequence [const restrict],
   const size_t sequence_length,
   size_t sequence_offset [const restrict static 1]
)
{
   ZoO_index i;

   *sequence_offset = 0;

   /*@
      loop invariant 0 <= i <= sequence_length;
      loop invariant (*sequence_offset <= i);
      loop invariant
      (
         (*sequence_offset == 0)
         || (sequence[*sequence_offset] == ZoO_START_OF_SEQUENCE_ID)
      );
      loop invariant
         (
            (i == 0) || (sequence[0 .. (i - 1)] == ZoO_START_OF_SEQUENCE_ID)
         );
      loop assigns i, *sequence_offset;
      loop variant (sequence_length - i);
   @*/
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
   const ZoO_index sequence_a [const],
   size_t sequence_a_length,
   const ZoO_index sequence_b [const],
   size_t sequence_b_length
)
{
   size_t min_length, a, b;
   size_t a_offset, b_offset;
   size_t i;
   /*@ ghost size_t actual_a_length, actual_b_length; @*/

   bypass_redundant_sos(sequence_a, sequence_a_length, &a_offset);
   bypass_redundant_sos(sequence_b, sequence_b_length, &b_offset);

   /*@ ghost actual_a_length = sequence_a_length; @*/
   /*@ ghost actual_b_length = sequence_b_length; @*/

   /*@ assert (a_offset <= sequence_a_length); @*/
   sequence_a_length -= a_offset;
   /*@ assert (b_offset <= sequence_b_length); @*/
   sequence_b_length -= b_offset;

   if (sequence_a_length < sequence_b_length)
   {
      min_length = sequence_a_length;
   }
   else
   {
      min_length = sequence_b_length;
   }

   /*@ assert (min_length <= sequence_a_length); @*/
   /*@ assert (min_length <= sequence_b_length); @*/

   /*@ assert (min_length + a_offset <= actual_a_length); @*/
   /*@ assert (min_length + b_offset <= actual_b_length); @*/

   /*@
      loop invariant 0 <= i <= min_length;
      loop assigns i;
      loop variant (min_length - i);
   @*/
   for (i = 0; i < min_length; ++i)
   {
      /*@ assert ((i + a_offset) < actual_a_length); @*/
      a = sequence_a[i + a_offset];
      /*@ assert ((i + b_offset) < actual_b_length); @*/
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

