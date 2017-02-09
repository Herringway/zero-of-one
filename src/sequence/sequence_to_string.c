#define _POSIX_C_SOURCE 200809L
#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/char.h"
#include "../core/index.h"

#include "../error/error.h"

#include "../knowledge/knowledge.h"

#include "sequence.h"

/******************************************************************************/
/** MEMORY ALLOCATION *********************************************************/
/******************************************************************************/
static int ensure_string_capacity
(
   ZoO_char * string [const restrict static 1],
   size_t string_capacity [const restrict static 1],
   const size_t string_required_capacity,
   FILE io [const restrict static 1]
)
{
   ZoO_char * new_string;

   if (string_required_capacity <= *string_capacity)
   {
      return 0;
   }

   new_string =
      (ZoO_char *) realloc
      (
         (void *) *string,
         ((size_t) string_required_capacity) * sizeof(ZoO_char)
      );

   if (new_string== (ZoO_char *) NULL)
   {
      ZoO_S_ERROR
      (
         io,
         "Unable to reallocate memory to match string's required size."
      );

      return -1;
   }

   *string_capacity = string_required_capacity;
   *string = new_string;

   return 1;
}

/******************************************************************************/
/** ADD WORD ******************************************************************/
/******************************************************************************/
static int increment_required_capacity
(
   size_t current_capacity [const restrict static 1],
   const size_t increase_factor,
   FILE io [const restrict static 1]
)
{
   if ((ZoO_INDEX_MAX - increase_factor) < *current_capacity)
   {
      ZoO_S_ERROR
      (
         io,
         "String capacity increment aborted, as the new capacity would not"
         " fit in a ZoO_index variable."
      );

      return -1;
   }

   *current_capacity += increase_factor;

   if ((SIZE_MAX / sizeof(ZoO_char)) < *current_capacity)
   {
      *current_capacity -= increase_factor;

      ZoO_S_ERROR
      (
         io,
         "String capacity increment aborted, as the new size would not fit"
         " in a size_t variable."
      );

      return -2;
   }

   return 0;
}

static int add_word
(
   const ZoO_index word_id,
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_char * destination [const restrict static 1],
   size_t destination_capacity [const restrict static 1],
   size_t destination_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
	const ZoO_char * word;
	ZoO_index word_size;
   size_t insertion_point;

   if (word_id < ZoO_RESERVED_IDS_COUNT)
   {
      return 0;
   }

	(void) ZoO_knowledge_lock_access(k, io);
	ZoO_knowledge_get_word(k, word_id, &word, &word_size);
	(void) ZoO_knowledge_unlock_access(k, io);

   insertion_point = *destination_length;

   /* word_size includes '\n', which will be replaced by a space. */
   /* (word_size == ZoO_INDEX_MAX) ==> could not have learned word. */
   if (increment_required_capacity(destination_length, (word_size + 1), io) < 0)
   {
      return -1;
   }

   if
   (
      ensure_string_capacity
      (
         destination,
         destination_capacity,
         *destination_length,
         io
      ) < 0
   )
   {
      return -2;
   }

   memcpy
   (
      (*destination + insertion_point),
      (const void *) word,
      word_size
   );

   (*destination)[*destination_length - 1] = ' ';

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/
int ZoO_sequence_to_undercase_string
(
   const ZoO_index sequence [const restrict static 1],
   const size_t sequence_length,
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_char * destination [const restrict static 1],
   size_t destination_capacity [const restrict static 1],
   size_t destination_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   size_t i;

   *destination_length = 0;

   for (i = 0; i < sequence_length; ++i)
   {
      if
      (
         add_word
         (
            sequence[i],
            k,
            destination,
            destination_capacity,
            destination_length,
            io
         ) < 0
      )
      {
         *destination_length = 0;

         return -1;
      }
   }

   return 0;
}
