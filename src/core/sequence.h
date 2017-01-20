#ifndef _ZoO_CORE_SEQUENCE_H_
#define _ZoO_CORE_SEQUENCE_H_

#include "../core/char_types.h"
#include "../core/index_types.h"

#include "../pipe/pipe.h"

#include "../knowledge/knowledge_types.h"

#include "sequence_types.h"

int ZoO_sequence_from_undercase_string
(
   const ZoO_char string [const restrict],
   const ZoO_index string_length,
   struct ZoO_knowledge k [const restrict static 1],
   ZoO_index * sequence [const restrict static 1],
   ZoO_index sequence_length [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
);

/*
 * Creates a sequence containing {initial_word}. The remaining elements of
 * sequence are added according to what is known to {k} as being possible.
 * The resulting sequence starts by ZoO_START_OF_SEQUENCE_ID, and ends by
 * ZoO_END_OF_SEQUENCE_ID. The sequence is allocated by the function. If an
 * error occur, it is unallocated and set to NULL ({sequence_size} is set
 * accordingly).
 * Return:
 *    0 on success.
 *    -1 iff the allocating failed.
 *    -2 iff the sequence initialization failed.
 *    -3 iff an error occured when trying to add elements to the right of the
 *       sequence.
 *    -4 iff an error occured when trying to add elements to the left of the
 *       sequence.
 *    -5 iff the resulting sequence would have been empty.
 * Pre:
 *    (> {markov_order} 0)
 *    (knows {k} {initial_word})
 *    (initialized {k})
 */
int ZoO_sequence_create_from
(
   const ZoO_index initial_word,
   ZoO_index credits [const restrict],
   const struct ZoO_knowledge k [const restrict static 1],
   const ZoO_index markov_order,
   ZoO_index * sequence [const restrict static 1],
   size_t sequence_size [const restrict static 1],
   const struct ZoO_pipe io [const restrict static 1]
);

/*
 * Compares two sequences.
 * ZoO_END_OF_SEQUENCE marks the ending of a sequence, regardless of indicated
 * sequence length, meaning that [10][ZoO_END_OF_SEQUENCE][9] and
 * [10][ZoO_END_OF_SEQUENCE][8] are considered equal. Sequences do not have to
 * contain ZoO_END_OF_SEQUENCE. [10][ZoO_END_OF_SEQUENCE] and [10] are
 * considered different, [10][ZoO_END_OF_SEQUENCE]
 * and [10][ZoO_END_OF_SEQUENCE][ZoO_END_OF_SEQUENCE] are considered equal.
 * Same logic is applyied for ZoO_START_OF_SEQUENCE:
 * [START_OF_SEQUENCE][10] is not [10], but
 * [START_OF_SEQUENCE][START_OF_SEQUENCE][10] and [START_OF_SEQUENCE][10] are
 * the same.
 * Return:
 *    1 iff {sequence_a} should be considered being more than {sequence_b}
 *    0 iff {sequence_a} should be considered being equal to {sequence_b}
 *    -1 iff {sequence_a} should be considered being less than {sequence_b}
 */
int ZoO_sequence_cmp
(
   const ZoO_index sequence_a [const],
   const ZoO_index sequence_a_length,
   const ZoO_index sequence_b [const],
   const ZoO_index sequence_b_length
);

#endif
