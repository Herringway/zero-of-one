#ifndef _ZoO_KNOWLEDGE_KNOWLEDGE_H_
#define _ZoO_KNOWLEDGE_KNOWLEDGE_H_

#include "../core/char_types.h"
#include "../core/index_types.h"

#include "../error/error.h"

#include "knowledge_types.h"

/*@
   requires \valid(k);
   requires \separated(k, io);

// Do not use if lock is already yours.
   requires (k->mutex == 1);

// Returns zero on success, -1 on failure.
   assigns \result;
   ensures ((\result == 0) || (\result == -1));

// On success, lock is acquired.
   ensures ((\result == 0) ==> (k->mutex == 0));

// Changes the status of the lock.
   assigns (k->mutex);
@*/
int ZoO_knowledge_lock_access
(
   struct ZoO_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

/*@
   requires \valid(k);
   requires \separated(k, io);

// Do not use if lock is not yours.
   requires (k->mutex == 0);

// Lock is released.
   ensures (k->mutex == 1);

// Changes the status of the lock.
   assigns (k->mutex);
@*/
void ZoO_knowledge_unlock_access
(
   struct ZoO_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

/*@
   requires (\block_length(k) >= 1);

// Returns zero on success, -1 on failure.
   assigns \result;
   ensures ((\result == 0) || (\result == -1));

// On success, all fields of {*k} are set.
   ensures ((\result == 0) ==> \valid(k));

// On success, the two reserved words are learnt.
   ensures ((\result == 0) ==> (k->words_length == 2));

// On success, the mutex is initialized and unlocked.
   ensures ((\result == 0) ==> (k->mutex == 1));

// At least some fields of k are set in any case.
   assigns (*k);
@*/
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
   FILE io [const restrict static 1]
);

int ZoO_knowledge_learn_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence [const restrict static 1],
   const size_t sequence_length,
   const ZoO_index markov_order,
   FILE io [const restrict static 1]
);

int ZoO_knowledge_learn_markov_sequence
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence [const restrict static 1],
   const ZoO_index markov_order, /* Pre (> markov_order 1) */
   ZoO_index sequence_id [const restrict static 1],
   FILE io [const restrict static 1]
);

void ZoO_knowledge_get_word
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index word_ref,
   const ZoO_char * word [const restrict static 1],
   ZoO_index word_length [const restrict static 1]
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

int ZoO_knowledge_rarest_word
(
   const struct ZoO_knowledge k [const static 1],
   const ZoO_index sequence [const restrict static 1],
   const size_t sequence_length,
   ZoO_index word_id [const restrict static 1]
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
   FILE io [const restrict static 1]
);

int ZoO_knowledge_strengthen_swt
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index sequence_id,
   const ZoO_index word_id,
   const ZoO_index target_id,
   FILE io [const restrict static 1]
);

int ZoO_knowledge_strengthen_tws
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index target_id,
   const ZoO_index word_id,
   const ZoO_index sequence_id,
   FILE io [const restrict static 1]
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
   FILE io [const restrict static 1]
);

int ZoO_knowledge_weaken_tws
(
   struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index target_id,
   const ZoO_index word_id,
   const ZoO_index sequence_id,
   FILE io [const restrict static 1]
);
*/
#endif
