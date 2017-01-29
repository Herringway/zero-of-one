#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/index.h"

#include "../pipe/pipe.h"

#include "sequence.h"

/******************************************************************************/
/** MEMORY (RE)ALLOCATION *****************************************************/
/******************************************************************************/

/*@
   requires \valid(required_capacity);
   requires \valid(io);
   requires (*required_capacity >= 0);
   requires (*required_capacity <= SIZE_MAX);
   requires \separated(required_capacity, io);

   assigns \result;

   ensures (*required_capacity >= 0);

   behavior success:
      assigns (*required_capacity);

      ensures (\result >= 0);
      ensures ((*required_capacity) == (\old(*required_capacity) + 1));
      ensures (((*required_capacity) * sizeof(ZoO_index)) <= SIZE_MAX);

   behavior failure:
      assigns \nothing;

      ensures (\result < 0);

   complete behaviors;
   disjoint behaviors;
@*/
static int increment_required_capacity
(
   size_t required_capacity [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   if
   (
      (*required_capacity == SIZE_MAX)
      || ((SIZE_MAX / sizeof(ZoO_index)) <= (*required_capacity + 1))
   )
   {
      /*@ assert \valid(io); @*/
      /*@ ghost return -1; @*/
      ZoO_S_ERROR
      (
         io,
         "Sequence capacity increment aborted, as the new size would not fit"
         " in a size_t variable."
      );

      return -1;
   }

   /*@ assert ((*required_capacity) < SIZE_MAX); @*/
   /*@ assert \valid(required_capacity); @*/
   *required_capacity = (*required_capacity + 1);

   /* assert (((*required_capacity) * sizeof(ZoO_index)) <= SIZE_MAX); @*/

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

int ZoO_sequence_ensure_capacity
(
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   const size_t sequence_required_capacity,
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index * new_sequence;

   if (sequence_required_capacity <= *sequence_capacity)
   {
      return 0;
   }

   /*@
      assert
      (
         sequence_required_capacity
         <= (SIZE_MAX / sizeof(ZoO_index))
      );
   @*/
   /*@ assert \valid(sequence); @*/
   /*@ assert \valid(*sequence); @*/

   new_sequence =
      (ZoO_index *) realloc
      (
         (void *) *sequence,
         (sequence_required_capacity * sizeof(ZoO_index))
      );

   if (new_sequence == (ZoO_index *) NULL)
   {
      /*@ assert \valid(io); @*/
      /*@ ghost return -1; @*/

      ZoO_S_ERROR
      (
         io,
         "Unable to reallocate memory to match sequence's required size."
      );

      return -1;
   }

   *sequence_capacity = sequence_required_capacity;
   *sequence = new_sequence;

   return 1;
}

int ZoO_sequence_append_left
(
   const ZoO_index word_id,
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   if (increment_required_capacity(sequence_length, io) < 0)
   {
      return -1;
   }

   /*@ assert (((*sequence_length) * sizeof(ZoO_index)) <= SIZE_MAX); @*/
   if
   (
      /* Appears to make Frama-C forget everything about *sequence_length. */
      ZoO_sequence_ensure_capacity
      (
         sequence,
         sequence_capacity,
         *sequence_length,
         io
      ) < 0
   )
   {
      return -2;
   }
   /*@ assert *sequence_length >= 0; @*/

   if (*sequence_length > 1)
   {
      /*@ assert(((*sequence_length) * sizeof(ZoO_index)) <= SIZE_MAX); @*/

      memmove
      (
         (void *) (*sequence + 1),
         (const void *) sequence,
         (((*sequence_length) - 1) * sizeof(ZoO_index))
      );
   }

   (*sequence)[0] = word_id;

   return 0;
}

int ZoO_sequence_append_right
(
   ZoO_index * sequence [const restrict static 1],
   const ZoO_index word_id,
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   if (increment_required_capacity(sequence_length, io) < 0)
   {
      return -1;
   }

   /*@ assert ((*sequence_length * sizeof(ZoO_index)) < SIZE_MAX); @*/
   if
   (
      ZoO_sequence_ensure_capacity
      (
         sequence,
         sequence_capacity,
         *sequence_length,
         io
      ) < 0
   )
   {
      return -1;
   }

   /* assert (*sequence_length >= 1) */
   (*sequence)[*sequence_length - 1] = word_id;

   return 0;
}
