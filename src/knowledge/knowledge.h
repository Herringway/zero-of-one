#ifndef _ZoO_KNOWLEDGE_KNOWLEDGE_H_
#define _ZoO_KNOWLEDGE_KNOWLEDGE_H_

#include "../core/char_types.h"
#include "../core/index_types.h"

#include "../pipe/pipe_types.h"

#include "knowledge_types.h"

int ZoO_knowledge_lock_access
(
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
);

void ZoO_knowledge_unlock_access
(
   struct ZoO_knowledge k [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
);

int ZoO_knowledge_initialize (struct ZoO_knowledge k [const restrict static 1]);

void ZoO_knowledge_finalize (struct ZoO_knowledge k [const restrict static 1]);

/*
 * When returning 0:
 *    {word} was added to {k}, or was already there.
 *    {*result} indicates where {word} is in {k->words}.
 *
 * When returning -1:
 *    Something went wrong when adding the occurrence of {word} to {k}.
 *    {k} remains semantically unchanged.
 *    {*result} may or may not have been altered.
 */
int ZoO_knowledge_learn_word
(
   struct ZoO_knowledge k [const static 1],
   const ZoO_char word [const restrict static 1],
   const size_t word_length,
   ZoO_index result [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
);

int ZoO_knowledge_learn_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence [const restrict static 1],
   const size_t sequence_length,
   const ZoO_index markov_order,
   const struct ZoO_pipe io [const restrict static 1]
);

int ZoO_knowledge_learn_markov_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index markov_order, /* Pre (> markov_order 1) */
   ZoO_index sequence_id [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
);

int ZoO_knowledge_get_word
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index word_ref,
   const ZoO_char * word [const restrict static 1],
   ZoO_index word_size [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
);

/*
 * When returning 0:
 *    {word} is in {k}.
 *    {word} is located at {k->words[*result]}.
 *
 * When returning -1:
 *    {word} is not in {k}.
 *    {*result} is where {word} was expected to be found in
 *    {k->sorted_indices}.
 */
int ZoO_knowledge_find_word_id
(
   const struct ZoO_knowledge k [const restrict static 1],
   const ZoO_char word [const restrict static 1],
   const size_t word_size,
   ZoO_index result [const restrict static 1]
);

int ZoO_knowledge_find_sequence
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index markov_order, /* Pre: (> 1) */
   ZoO_index sequence_id [const restrict static 1]
);

int ZoO_knowledge_find_markov_sequence
(
   const ZoO_index sequence_id,
   const struct ZoO_knowledge_sequence_collection sc [const restrict static 1],
   ZoO_index result [const restrict static 1]
);

int ZoO_knowledge_find_sequence_target
(
   const ZoO_index target_id,
   const struct ZoO_knowledge_sequence_data sd [const restrict static 1],
   ZoO_index result [const restrict static 1]
);

int ZoO_knowledge_random_tws_target
(
   const struct ZoO_knowledge k [const static 1],
   ZoO_index target [const restrict static 1],
   const ZoO_index word_id,
   const ZoO_index sequence_id
);

int ZoO_knowledge_random_swt_target
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence_id,
   const ZoO_index word_id,
   ZoO_index target [const restrict static 1]
);

int ZoO_knowledge_copy_random_swt_sequence
(
   const struct ZoO_knowledge k [const static 1],
   ZoO_index sequence [const restrict static 1],
   const ZoO_index word_id,
   const ZoO_index markov_order,
   const struct ZoO_pipe io [const restrict static 1]
);

int ZoO_knowledge_strengthen_swt
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence_id,
   const ZoO_index word_id,
   const ZoO_index target_id,
   const struct ZoO_pipe io [const restrict static 1]
);

int ZoO_knowledge_strengthen_tws
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index target_id,
   const ZoO_index word_id,
   const ZoO_index sequence_id,
   const struct ZoO_pipe io [const restrict static 1]
);

/*
 * TODO
 */
/*
int ZoO_knowledge_weaken_swt
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence_id,
   const ZoO_index word_id,
   const ZoO_index target_id,
   const struct ZoO_pipe io [const restrict static 1]
);

int ZoO_knowledge_weaken_tws
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index target_id,
   const ZoO_index word_id,
   const ZoO_index sequence_id,
   const struct ZoO_pipe io [const restrict static 1]
);
*/
#endif
