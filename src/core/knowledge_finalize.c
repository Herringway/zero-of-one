#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../io/error.h"

#include "knowledge.h"

void knowledge_sequence_collection_finalize
(
   struct ZoO_knowledge_sequence_collection c [const restrict static 1]
)
{
   ZoO_index i;

   if (c->sequences_ref != (ZoO_index *) NULL)
   {
      free((void *) c->sequences_ref);
      c->sequences_ref = (ZoO_index *) NULL;
   }

   if (c->sequences_ref_sorted != (ZoO_index *) NULL)
   {
      free((void *) c->sequences_ref_sorted);
      c->sequences_ref_sorted = (ZoO_index *) NULL;
   }

   if (c->occurrences != (ZoO_index *) NULL)
   {
      free((void *) c->occurrences);
      c->occurrences = (ZoO_index *) NULL;
   }

   for (i = 0; i < c->sequences_ref_length; ++i)
   {
      free((void *) c->targets[i]);
      free((void *) c->targets_occurrences[i]);
   }

   c->sequences_ref_length = 0;

   if (c->targets != (ZoO_index **) NULL)
   {
      free((void *) c->targets);
      c->targets != (ZoO_index **) NULL;
   }

   free((void *) c->targets_length);

   if (c->targets_occurrences != (ZoO_index **) NULL)
   {
      free((void *) c->targets_occurrences);
      c->targets_occurrences != (ZoO_index **) NULL;
   }
}

void knowledge_word_finalize
(
   struct ZoO_knowledge_word w [const restrict static 1]
)
{
   w->word_size = 0;
   w->occurrences = 0;

   if (w->word != (ZoO_char *) NULL)
   {
      free((void *) w->word);

      w->word = (ZoO_char *) NULL;
   }

   knowledge_sequence_collection_finalize(&(w->followed));
   knowledge_sequence_collection_finalize(&(w->preceded));
}

void ZoO_knowledge_finalize (struct ZoO_knowledge k [const restrict static 1])
{
   ZoO_index i;

   for (i = 0; i < k->words_length; ++i)
   {
      knowledge_word_finalize(k->words + i);
   }

   k->words_length = 0;

   if (k->words != (struct ZoO_knowledge_word *) NULL)
   {
      free((void *) k->words);

      k->words = (struct ZoO_knowledge_word *) NULL;
   }

   if (k->words_sorted != (ZoO_index *) NULL)
   {
      free((void *) k->words_sorted);

      k->words_sorted = (ZoO_index *) NULL;
   }

   for (i = 0; i < k->sequences_length; ++i)
   {
      free((void *) k->sequences[i]);
   }

   k->sequences_length = 0;

   if (k->sequences != (ZoO_index **) NULL)
   {
      free((void *) k->sequences);

      k->sequences = (ZoO_index **) NULL;
   }

   if (k->sequences_sorted != (ZoO_index *) NULL)
   {
      free((void *) k->sequences_sorted);

      k->sequences_sorted = (ZoO_index *) NULL;
   }
}
