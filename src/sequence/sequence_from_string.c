#define _POSIX_C_SOURCE 200809L
#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/char.h"
#include "../core/index.h"

#include "../pipe/pipe.h"

#include "../knowledge/knowledge.h"

#include "sequence.h"

/******************************************************************************/
/** HANDLING WORDS ************************************************************/
/******************************************************************************/

static int add_word_to_sequence
(
   const ZoO_char string [const restrict static 1],
   const size_t word_start,
   const size_t word_length,
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index word_id;
   ZoO_char * stored_word;

   if (word_length == 0)
   {
      return 0;
   }

   (void) ZoO_knowledge_lock_access(k, io);

   if
   (
      ZoO_knowledge_learn_word
      (
         k,
         (string + word_start),
         word_length,
         &word_id,
         io
      ) < 0
   )
   {
      (void) ZoO_knowledge_unlock_access(k, io);

      return -1;
   }

   (void) ZoO_knowledge_unlock_access(k, io);

   if
   (
      ZoO_sequence_append_right
      (
         sequence,
         word_id,
         sequence_capacity,
         sequence_length,
         io
      ) < 0
   )
   {
      return -1;
   }

   return 0;
}

static int find_word
(
   const ZoO_char string [const restrict static 1],
   const size_t string_length,
   const size_t offset,
   size_t word_start [const restrict static 1],
   size_t word_length [const restrict static 1]
)
{
   size_t i;

   i = offset;

   while ((string[i] == ' ') && (i < string_length))
   {
      i += 1;
   }

   if (i >= string_length)
   {
      return -1;
   }

   *word_start = i;

   while ((string[i] != ' ') && (i < string_length))
   {
      i += 1;
   }

   if (i >= string_length)
   {
      return -1;
   }

   *word_length = (i - *word_start);

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

/* See: "sequence.h" */
int ZoO_sequence_from_undercase_string
(
   const ZoO_char string [const restrict],
   const size_t string_length,
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   size_t word_start, word_length;
   size_t i;

   i = 0;

   *sequence = (ZoO_index *) NULL;
   *sequence_length = 0;

   if
   (
      ZoO_sequence_append_right
      (
         sequence,
         ZoO_START_OF_SEQUENCE_ID,
         sequence_capacity,
         sequence_length,
         io
      ) < 0
   )
   {
      return -1;
   }

   while (i < string_length)
   {
      if (find_word(string, i, string_length, &word_start, &word_length) < 0)
      {
         break;
      }

      if
      (
         add_word_to_sequence
         (
            string,
            word_start,
            word_length,
            sequence,
            sequence_capacity,
            sequence_length,
            k,
            io
         ) < 0
      )
      {
         free((void *) *sequence);
         *sequence = (ZoO_index *) NULL;
         *sequence_length = 0;

         return -1;
      }

      i = (word_start + word_length);
   }

   if
   (
      ZoO_sequence_append_right
      (
         sequence,
         ZoO_END_OF_SEQUENCE_ID,
         sequence_capacity,
         sequence_length,
         io
      ) < 0
   )
   {
      free((void *) *sequence);

      *sequence = (ZoO_index *) NULL;
      *sequence_length = 0;

      return -1;
   }

   return 0;
}
