#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/sequence.h"

#include "../pipe/pipe.h"

#include "knowledge.h"

/******************************************************************************/
/** INITIALIZE ****************************************************************/
/******************************************************************************/
static void set_nth_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sorted_sequence_id,
   const ZoO_index sequence_id
)
{
   /* Safe: (> k->sequences_length 1) */
   if (sorted_sequence_id < (k->sequences_length - 1))
   {
      memmove
      (
         /* Safe: (=< (+ sorted_sequence_id 1) k->sequences_length) */
         (void *) (k->sequences_sorted + (sorted_sequence_id + 1)),
         (const void *) (k->sequences_sorted + sorted_sequence_id),
         ((k->sequences_length - 1) - sorted_sequence_id)
      );
   }

   k->sequences_sorted[sorted_sequence_id] = sequence_id;
}

/******************************************************************************/
/** ALLOCATING MEMORY *********************************************************/
/******************************************************************************/
static int reallocate_sequences_list
(
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index ** new_sequences;

   if ((SIZE_MAX / sizeof(ZoO_index *)) > (size_t) k->sequences_length)
   {
      ZoO_S_ERROR
      (
         io,
         "Unable to store the size of the sequences list, as it would overflow"
         "size_t variables."
      );

      return -1;
   }

   new_sequences =
      (ZoO_index **) realloc
      (
         (void *) k->sequences,
         (((size_t) k->sequences_length) * sizeof(ZoO_index *))
      );

   if (new_sequences == (ZoO_index **) NULL)
   {
      ZoO_S_ERROR
      (
         io,
         "Unable to allocate the memory required for the new sequence list."
      );

      return -1;
   }

   k->sequences = new_sequences;

   return 0;
}

static int reallocate_sequences_sorted_list
(
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index * new_sequences_sorted;

   if ((SIZE_MAX / sizeof(ZoO_index)) > (size_t) k->sequences_length)
   {
      ZoO_S_ERROR
      (
         io,
         "Unable to store the size of the sorted sequences list, as it would"
         " overflow size_t variables."
      );

      return -1;
   }

   new_sequences_sorted =
      (ZoO_index *) realloc
      (
         (void *) k->sequences_sorted,
         ((size_t) k->sequences_length) * sizeof(ZoO_index)
      );

   if (new_sequences_sorted == (ZoO_index *) NULL)
   {
      ZoO_S_ERROR
      (
         io,
         "Unable to allocate the memory required for the new sorted sequences"
         " list."
      );

      return -1;
   }

   k->sequences_sorted = new_sequences_sorted;

   return 0;
}

/* Pre: (=< ZoO_INDEX_MAX SIZE_MAX) */
/*@
   requires
   (
      (base_length == destination_length)
      ||
      (
         (base_length < destination_length)
         &&
         (
           (base[0] == ZoO_START_OF_SEQUENCE)
           (base[base_length - 1] == ZoO_END_OF_SEQUENCE)
         )
      )
   );
@*/
static ZoO_index * copy_sequence
(
   const ZoO_index base [const restrict static 1],
   const ZoO_index base_length,
   const ZoO_index destination_length,
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index i, diff;
   ZoO_index * result;

   result =
      (ZoO_index *) calloc
      (
         (size_t) (destination_length),
         sizeof(ZoO_index)
      );

   if (result == (ZoO_index *) NULL)
   {
      ZoO_S_ERROR
      (
         io,
         "Unable to allocate the memory required to store a new sequence."
      );

      return (ZoO_index *) NULL;
   }

   if (base_length == destination_length)
   {
      memcpy
      (
         (void *) result,
         (const void *) base,
         (((size_t) base_length) * sizeof(ZoO_index))
      );
   }
   else if (base[0] == ZoO_START_OF_SEQUENCE_ID)
   {
      diff = (destination_length - base_length);

      memcpy
      (
         (void *) (result + diff),
         (const void *) base,
         (((size_t) base_length) * sizeof(ZoO_index))
      );

      for (i = 0; i < diff; ++i)
      {
         result[i] = ZoO_START_OF_SEQUENCE_ID;
      }
   }
   else if (base[(base_length - 1)] == ZoO_END_OF_SEQUENCE_ID)
   {
      memcpy
      (
         (void *) result,
         (const void *) base,
         (((size_t) base_length) * sizeof(ZoO_index))
      );

      for (i = base_length; i < destination_length; ++i)
      {
         result[i] = ZoO_END_OF_SEQUENCE_ID;
      }
   }

   return result;
}

/******************************************************************************/
/** ADD A NEW SEQUENCE ********************************************************/
/******************************************************************************/

static int add_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index sequence_length,
   const ZoO_index markov_order, /* Pre (> markov_order 1) */
   const ZoO_index sequence_id,
   const ZoO_index sorted_sequence_id,
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index * stored_sequence;

   if (k->sequences_length == ZoO_INDEX_MAX)
   {
      ZoO_S_ERROR
      (
         io,
         "Unable to add sequence: the variable that stores the number of known "
         "sequences would overflow."
      );

      return -1;
   }

   stored_sequence = copy_sequence(sequence, sequence_length, markov_order, io);

   if (stored_sequence == (ZoO_index *) NULL)
   {
      return -1;
   }

   k->sequences_length += 1;

   if (reallocate_sequences_list(k, io) < 0)
   {
      k->sequences_length -= 1;

      free((void *) stored_sequence);

      return -1;
   }

   k->sequences[sequence_id] = stored_sequence;

   if (reallocate_sequences_sorted_list(k, io) < 0)
   {
      k->sequences_length -= 1;

      free((void *) stored_sequence);

      return -1;
   }

   set_nth_sequence(k, sorted_sequence_id, sequence_id);

   return 0;
}

/******************************************************************************/
/** SEARCH EXISTING SEQUENCES *************************************************/
/******************************************************************************/

static int find_sequence
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index sequence_length,
   const ZoO_index markov_order, /* Pre: (> 1) */
   ZoO_index sequence_id [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   ZoO_index i, current_min, current_max;
   const ZoO_index markov_sequence_length = (markov_order - 1);

   /* Handles the case where the list is empty ********************************/
   current_max = k->sequences_length;

   if (current_max == 0)
   {
      *sequence_id = 0;

      return -1;
   }
   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   for (;;)
   {
      i = (current_min + ((current_max - current_min) / 2));

      cmp =
         ZoO_sequence_cmp
         (
            k->sequences[k->sequences_sorted[i]],
            markov_sequence_length,
            sequence,
            sequence_length
         );

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *sequence_id = current_min;

            return -1;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min > current_max) || (i == 0))
         {
            *sequence_id = i;

            return -1;
         }

         current_max = (i - 1);
      }
      else
      {
         *sequence_id = k->sequences_sorted[i];

         return 0;
      }
   }
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

int ZoO_knowledge_learn_markov_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index sequence_length,
   const ZoO_index markov_order, /* Pre (> markov_order 1) */
   ZoO_index sequence_id [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index sorted_id;

   if
   (
      find_sequence
      (
         k,
         sequence,
         sequence_length,
         markov_order,
         sequence_id
      ) == 0
   )
   {
      return 0;
   }

   sorted_id = *sequence_id;
   *sequence_id = k->sequences_length;

   return
      add_sequence
      (
         k,
         sequence,
         sequence_length,
         markov_order,
         *sequence_id,
         sorted_id,
         io
      );
}
