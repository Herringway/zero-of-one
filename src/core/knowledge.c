#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../io/error.h"

#include "knowledge.h"

/** Basic functions of the ZoO_knowledge structure ****************************/
void ZoO_knowledge_initialize (struct ZoO_knowledge k [const static 1])
{
   k->words = (struct ZoO_knowledge_word *) NULL;
   k->words_length = 0;
   k->words_sorted = (ZoO_index *) NULL;
}
