#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../pipe/pipe.h"

#include "knowledge.h"

/** Basic functions of the ZoO_knowledge structure ****************************/

/* See: "knowledge.h" */
int ZoO_knowledge_initialize (struct ZoO_knowledge k [const restrict static 1])
{
   int error;

   k->words = (struct ZoO_knowledge_word *) NULL;
   k->words_length = 0;
   k->words_sorted = (ZoO_index *) NULL;

   k->sequences = (ZoO_index **) NULL;
   k->sequences_length = 0;
   k->sequences_sorted = (ZoO_index *) NULL;

   error = pthread_mutex_init(&(k->mutex), (const pthread_mutexattr_t *) NULL);

   if (error != 0)
   {
      fprintf
      (
         stderr,
         "[F] Unable to initialize knowledge mutex: %s.\n",
         strerror(error)
      );

      return -1;
   }

   return 0;
}

int ZoO_knowledge_lock_access
(
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   return pthread_mutex_lock(&(k->mutex));
}

void ZoO_knowledge_unlock_access
(
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
)
{
   pthread_mutex_unlock(&(k->mutex));
}
