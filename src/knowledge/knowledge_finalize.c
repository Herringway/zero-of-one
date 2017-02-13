#include <stdlib.h>

#include "knowledge.h"

/*@
   requires \valid(sd);
@*/
static void knowledge_sequence_data_finalize
(
   struct ZoO_knowledge_sequence_data sd [const restrict static 1]
)
{
   sd->occurrences = 0;

   if (sd->targets != (struct ZoO_knowledge_target *) NULL)
   {
      free((void *) sd->targets);

      sd->targets = (struct ZoO_knowledge_target *) NULL;
   }

   sd->targets_length = 0;

}

static void knowledge_sequence_collection_finalize
(
   struct ZoO_knowledge_sequence_collection c [const restrict static 1]
)
{
   ZoO_index i;

   for (i = 0; i < c->sequences_ref_length; ++i)
   {
      knowledge_sequence_data_finalize(c->sequences_ref + i);
   }

   if (c->sequences_ref != (struct ZoO_knowledge_sequence_data *) NULL)
   {
      free((void *) c->sequences_ref);

      c->sequences_ref = (struct ZoO_knowledge_sequence_data *) NULL;
   }

   if (c->sequences_ref_sorted != (ZoO_index *) NULL)
   {
      free((void *) c->sequences_ref_sorted);

      c->sequences_ref_sorted = (ZoO_index *) NULL;
   }

   c->sequences_ref_length = 0;
}

static void knowledge_word_finalize
(
   struct ZoO_knowledge_word w [const restrict static 1]
)
{
   w->word_length = 0;
   w->occurrences = 0;

   if (w->word != (ZoO_char *) NULL)
   {
      free((void *) w->word);

      w->word = (ZoO_char *) NULL;
   }

   knowledge_sequence_collection_finalize(&(w->swt));
   knowledge_sequence_collection_finalize(&(w->tws));
}

/* See: "knowledge.h" */
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

   pthread_mutex_destroy(&(k->mutex));
}
