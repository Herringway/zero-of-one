#ifndef _ZoO_CORE_KNOWLEDGE_H_
#define _ZoO_CORE_KNOWLEDGE_H_

#include "../tool/strings_types.h"

#include "knowledge_types.h"

/*
 * Initializes all of {k}'s members to sane values.
 *
 * When returning 0:
 *    Initial punctuation nodes (including the mandatory "START OF LINE" and
 *    "END OF LINE" ones) have successfully been added to {k}.
 *
 * When return -1:
 *    Something went wrong, leading to {k} not being safe for use.
 *    {k} has been finalized.
 */
int ZoO_knowledge_initialize (struct ZoO_knowledge k [const static 1]);

/*
 * Frees all the memory used by {k}, but not {k} itself.
 * The values of {k}'s members are set to reflect the changes.
 */
void ZoO_knowledge_finalize (struct ZoO_knowledge k [const static 1]);

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
int ZoO_knowledge_find
(
   const struct ZoO_knowledge k [const restrict static 1],
   const ZoO_char word [const restrict static 1],
   ZoO_index result [const restrict static 1]
);

/*
 * When returning 0:
 *    {word} was either added to {k} or its representation in {k} has its
 *    occurrences count increased.
 *    {*result} indicates where {word} is in {k->words}.
 *
 * When returning -1:
 *    Something went wrong when adding the occurrence of {word} to {k}.
 *    {k} remains semantically unchanged.
 *    {*result} may or may not have been altered.
 */
int ZoO_knowledge_learn
(
   struct ZoO_knowledge k [const static 1],
   const ZoO_char word [const restrict static 1],
   ZoO_index result [const restrict static 1]
);

int ZoO_knowledge_assimilate
(
   struct ZoO_knowledge k [const static 1],
   struct ZoO_strings string [const restrict static 1],
   ZoO_index const aliases_count,
   const char * restrict aliases [const restrict static aliases_count]
);

int ZoO_knowledge_extend
(
   struct ZoO_knowledge k [const static 1],
   const struct ZoO_strings string [const],
   int const ignore_first_word,
   ZoO_char * result [const static 1]
);

#endif
