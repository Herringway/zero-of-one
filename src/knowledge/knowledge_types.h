#ifndef _ZoO_KNOWLEDGE_KNOWLEDGE_TYPES_H_
#define _ZoO_KNOWLEDGE_KNOWLEDGE_TYPES_H_

#include <pthread.h>

#include "../core/index_types.h"
#include "../core/char_types.h"

struct ZoO_knowledge_sequence_collection
{
   ZoO_index * sequences_ref;
   ZoO_index sequences_ref_length;
   ZoO_index * sequences_ref_sorted;
   ZoO_index * occurrences;
   ZoO_index ** targets;
   ZoO_index * targets_length;
   ZoO_index ** targets_occurrences;
};

struct ZoO_knowledge_word
{
   const ZoO_char * word;
   ZoO_index word_length;
   ZoO_index occurrences;

   /* [Sequence] [Word] [Target] */
   struct ZoO_knowledge_sequence_collection swt;

   /* [Target] [Word] [Sequence] */
   struct ZoO_knowledge_sequence_collection tws;
};

struct ZoO_knowledge
{
   struct ZoO_knowledge_word * words;
   ZoO_index words_length;
   ZoO_index * words_sorted;
   ZoO_index ** sequences;
   ZoO_index sequences_length;
   ZoO_index * sequences_sorted;
   pthread_mutex_t mutex;
};

#endif
