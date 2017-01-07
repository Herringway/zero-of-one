#ifndef _ZoO_CORE_KNOWLEDGE_TYPES_H_
#define _ZoO_CORE_KNOWLEDGE_TYPES_H_

#include "../core/index_types.h"
#include "../core/char_types.h"

struct ZoO_knowledge_sequence_collection
{
   ZoO_index ** sequences;
   ZoO_index sequences_length;
   ZoO_index * sequences_sorted;
   ZoO_index * occurrences;
   ZoO_index ** targets;
   ZoO_index * targets_length;
   ZoO_index ** targets_occurrences;
};

struct ZoO_knowledge_word
{
   ZoO_char * word;
   size_t word_size;
   ZoO_index occurrences;
   struct ZoO_knowledge_sequence_collection followed;
   struct ZoO_knowledge_sequence_collection preceded;
};

struct ZoO_knowledge
{
   struct ZoO_knowledge_word * words;
   ZoO_index words_length;
   ZoO_index * words_sorted;
};

#endif
