#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../error/error.h"

#include "knowledge.h"

/** Basic functions of the ZoO_knowledge structure ****************************/

/* See: "knowledge.h" */
int ZoO_knowledge_initialize (struct ZoO_knowledge k [const restrict static 1])
{
   int error;
   ZoO_index reserved_word_id;

   k->words = (struct ZoO_knowledge_word *) NULL;
   k->words_length = 0;
   k->words_sorted = (ZoO_index *) NULL;

   k->sequences = (ZoO_index **) NULL;
   k->sequences_length = 0;
   k->sequences_sorted = (ZoO_index *) NULL;

#ifndef ZoO_RUNNING_FRAMA_C
   error = pthread_mutex_init(&(k->mutex), (const pthread_mutexattr_t *) NULL);
#else
   k->mutex = 1;
   error = 0;
#endif

   if (error != 0)
   {
      ZoO_FATAL
      (
         stderr,
         "Unable to initialize knowledge mutex: %s.",
         strerror(error)
      );

      return -1;
   }

   if
   (
      (
         ZoO_knowledge_learn_word
         (
            k,
            "[SoS]",
            5,
            &reserved_word_id,
            stderr
         ) < 0
      )
      ||
      (
         ZoO_knowledge_learn_word
         (
            k,
            "[EoS]",
            5,
            &reserved_word_id,
            stderr
         ) < 0
      )
   )
   {
      ZoO_S_FATAL(stderr, "Unable to learn reserved words.");

      return -1;
   }

   return 0;
}

int ZoO_knowledge_lock_access
(
   struct ZoO_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

#ifndef ZoO_RUNNING_FRAMA_C
   err = pthread_mutex_lock(&(k->mutex));
#else
   /*@ assert (k->mutex == 1); @*/
   k->mutex = 0;
   err = 0;
#endif

   if (err != 0)
   {
      ZoO_ERROR
      (
         io,
         "Unable to get exclusive access to knowledge: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

void ZoO_knowledge_unlock_access
(
   struct ZoO_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

#ifndef ZoO_RUNNING_FRAMA_C
   err = pthread_mutex_unlock(&(k->mutex));
#else
   /*@ assert (k->mutex == 0); @*/
   k->mutex = 1;
   err = 0;
#endif

   if (err != 0)
   {
      ZoO_ERROR
      (
         io,
         "Unable to release exclusive access to knowledge: %s",
         strerror(err)
      );
   }
}

void ZoO_knowledge_get_word
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index word_ref,
   const ZoO_char * word [const restrict static 1],
   ZoO_index word_length [const restrict static 1]
)
{
   *word = k->words[word_ref].word;
   *word_length = k->words[word_ref].word_length;
}

int ZoO_knowledge_rarest_word
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence [const restrict static 1],
   const size_t sequence_length,
   ZoO_index word_id [const restrict static 1]
)
{
   ZoO_index current_max_score;
   size_t i;
   int success;

   current_max_score = ZoO_INDEX_MAX;

   success = -1;

   for (i = 0; i < sequence_length; ++i)
   {
      if
      (
         (k->words[sequence[i]].occurrences <= current_max_score)
         /* Otherwise we might just have learned it, or it must not be used. */
         && (k->words[sequence[i]].occurrences > 1)
      )
      {
         current_max_score = k->words[sequence[i]].occurrences;
         *word_id = sequence[i];
         success = 0;
      }
   }

   return success;
}
