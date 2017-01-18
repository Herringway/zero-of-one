#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../cli/cli.h"

#include "knowledge.h"

/** Basic functions of the ZoO_knowledge structure ****************************/

/* See: "knowledge.h" */
void ZoO_knowledge_initialize (struct ZoO_knowledge k [const static 1])
{
   k->words = (struct ZoO_knowledge_word *) NULL;
   k->words_length = 0;
   k->words_sorted = (ZoO_index *) NULL;

   k->sequences = (ZoO_index **) NULL;
   k->sequences_length = 0;
   k->sequences_sorted = (ZoO_index *) NULL;
}
