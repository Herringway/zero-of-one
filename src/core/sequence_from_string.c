#define _POSIX_C_SOURCE 200809L
#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/char.h"
#include "../core/index.h"

#include "../pipe/pipe.h"

#include "../knowledge/knowledge.h"

#include "sequence.h"

static int add_word_id_to_sequence
(
   const ZoO_index word_id,
   ZoO_index * sequence [const restrict static 1],
   ZoO_index sequence_length [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index * new_sequence;

   *sequence_length += 1;

   new_sequence =
      (ZoO_index *) realloc
      (
         (void *) *sequence,
         (((size_t) sequence_length) * sizeof(ZoO_index))
      );

   if (new_sequence == (ZoO_index *) NULL)
   {
      ZoO_S_ERROR(io, "Unable to reallocate a sequence to add word ids to it.");

      return -1;
   }

   return 0;
}

/******************************************************************************/
/** HANDLING PUNCTUATION ******************************************************/
/******************************************************************************/

/*
 * Semaphore:
 *    Takes then releases access for {k}.
 */
static int add_punctuation_to_sequence
(
   const ZoO_char string [const restrict static 1],
   const ZoO_char punctuation,
   ZoO_index * sequence [const restrict static 1],
   ZoO_index sequence_length [const restrict static 1],
   const struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index word_id;
   ZoO_char as_word[2];

   as_word[0] = punctuation;
   as_word[1] = '\0';

   (void) ZoO_knowledge_lock_access(k, io);

   if (ZoO_knowledge_find_word_id(k, as_word, 2, &word_id, io) < 0)
   {
      (void) ZoO_knowledge_unlock_access(k, io);

      ZoO_PROG_ERROR
      (
         io,
         "'%s' was defined as a punctuation, was found in a string, yet is not"
         " defined in the knowledge database.",
         as_word
      );

      return -1;
   }

   (void) ZoO_knowledge_unlock_access(k, io);

   if (add_word_id_to_sequence(word_id, sequence, sequence_length, io) < 0)
   {
      return -1;
   }

   return 0;
}

static int word_is_punctuation_terminated
(
   const ZoO_char string [const restrict static 1],
   const ZoO_index word_start,
   const ZoO_index word_length
)
{
   return ZoO_char_is_punctuation(string[word_length]);
}

/******************************************************************************/
/** HANDLING WORDS ************************************************************/
/******************************************************************************/

/*
 * Semaphore:
 *    Takes then releases access for {k}.
 */
static int add_word_to_sequence
(
   const ZoO_char string [const restrict static 1],
   const ZoO_index word_start,
   const ZoO_index word_length,
   ZoO_index * sequence [const restrict static 1],
   ZoO_index sequence_length [const restrict static 1],
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

   if (add_word_id_to_sequence(word_id, sequence, sequence_length, io) < 0)
   {
      return -1;
   }

   return 0;
}

static int add_finding_to_sequence
(
   const ZoO_char string [const restrict static 1],
   const ZoO_index word_start,
   const ZoO_index word_length,
   ZoO_index * sequence [const restrict static 1],
   ZoO_index sequence_length [const restrict static 1],
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index punctuation;

   if (word_is_punctuation_terminated(string, word_start, word_length))
   {
      punctuation = 1;
   }
   else
   {
      punctuation = 0;
   }

   if
   (
      add_word_to_sequence
      (
         string,
         word_start,
         (word_length - punctuation),
         sequence,
         sequence_length,
         k,
         io
      ) < 0
   )
   {
      return -1;
   }

   if
   (
      (punctuation == 1)
      &&
      (
         add_punctuation_to_sequence
         (
            string,
            string[word_start + word_length - 1],
            sequence,
            sequence_length,
            k,
            io
         ) < 0
      )
   )
   {
      return -1;
   }

   return 0;
}

static int find_word
(
   const ZoO_char string [const restrict static 1],
   const ZoO_index string_length,
   const ZoO_index offset,
   ZoO_index word_start [const restrict static 1],
   ZoO_index word_length [const restrict static 1]
)
{
   ZoO_index i;

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
/******************************************************************************/a

/* See: "sequence.h" */
int ZoO_sequence_from_undercase_string
(
   const ZoO_char string [const restrict],
   const ZoO_index string_length,
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_index * sequence [const restrict static 1],
   ZoO_index sequence_length [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   ZoO_index word_start, word_length;
   ZoO_index i;

   i = 0;

   *sequence = (ZoO_index *) NULL;
   *sequence_length = 0;

   if
   (
      add_word_id_to_sequence
      (
         ZoO_START_OF_SEQUENCE_ID,
         sequence,
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
         add_finding_to_sequence
         (
            string,
            word_start,
            word_length,
            sequence,
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
      add_word_id_to_sequence
      (
         ZoO_END_OF_SEQUENCE_ID,
         sequence,
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
