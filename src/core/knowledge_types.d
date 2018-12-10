module core.knowledge_types;

import pervasive;

enum ZoO_WORD_START_OF_LINE = 0;
enum ZoO_WORD_END_OF_LINE = 1;

static if (ZoO_MARKOV_ORDER == 1)
   enum ZoO_SEQUENCE_SIZE = 1;
else
   enum ZoO_SEQUENCE_SIZE = ZoO_MARKOV_ORDER - 1;

enum ZoO_S_LINK_SIZE = ZoO_SEQUENCE_SIZE + 1;

enum ZoO_knowledge_special_effect
{
   ZoO_WORD_HAS_NO_EFFECT,
   ZoO_WORD_ENDS_SENTENCE,
   ZoO_WORD_STARTS_SENTENCE,
   ZoO_WORD_REMOVES_LEFT_SPACE,
   ZoO_WORD_REMOVES_RIGHT_SPACE
};

struct ZoO_knowledge_link
{
   ZoO_index[ZoO_SEQUENCE_SIZE] sequence;
   ZoO_index occurrences;
   ZoO_index* targets_occurrences;
   ZoO_index[] targets;
};

struct ZoO_knowledge_word
{
   size_t word_size;
   ZoO_char* word;
   ZoO_knowledge_special_effect special;
   ZoO_index occurrences;
   ZoO_index forward_links_count;
   ZoO_index backward_links_count;
   ZoO_knowledge_link* forward_links;
   ZoO_knowledge_link* backward_links;
};


struct ZoO_knowledge
{
   ZoO_index words_count;
   ZoO_index* sorted_indices;
   ZoO_knowledge_word* words;
};