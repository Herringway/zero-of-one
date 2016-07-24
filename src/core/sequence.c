#include <stdlib.h>
#include <string.h>

#include "../io/error.h"
#include "../tool/sorted_list.h"

#include "knowledge.h"

static int cmp_seq_link
(
   const void * const a,
   const void * const b,
   const void * const other
)
{
   ZoO_index j;
   ZoO_index * sequence;
   struct ZoO_knowledge_link * link;

   sequence = (ZoO_index *) a;
   link = (struct ZoO_knowledge_link *) b;

   for (j = 0; j < ZoO_SEQUENCE_SIZE; ++j)
   {
      if (sequence[j] < link->sequence[j])
      {
         return -1;
      }
      else if (sequence[j] > link->sequence[j])
      {
         return 1;
      }
   }

   return 0;
}

int ZoO_knowledge_find_link
(
   ZoO_index const links_count,
   struct ZoO_knowledge_link links [const],
   ZoO_index const sequence [const restrict static ZoO_SEQUENCE_SIZE],
   ZoO_index result [const restrict static 1]
)
{
   return
      ZoO_sorted_list_index_of
      (
         links_count,
         (void const *) links,
         (void const *) sequence,
         sizeof(struct ZoO_knowledge_link),
         cmp_seq_link,
         (void const *) NULL,
         result
      );
}

int ZoO_knowledge_get_link
(
   ZoO_index links_count [const],
   struct ZoO_knowledge_link * links [const],
   ZoO_index const sequence [const restrict static ZoO_SEQUENCE_SIZE],
   ZoO_index result [const restrict static 1]
)
{
   struct ZoO_knowledge_link * new_p;

   if
   (
      ZoO_sorted_list_index_of
      (
         *links_count,
         (void const *) *links,
         (void const *) sequence,
         sizeof(struct ZoO_knowledge_link),
         cmp_seq_link,
         (void const *) NULL,
         result
      ) == 0
   )
   {
      return 0;
   }

   *links_count += 1;

   new_p =
      (struct ZoO_knowledge_link *) realloc
      (
         (void *) *links,
         (sizeof(struct ZoO_knowledge_link) * (*links_count))
      );

   if (new_p == (struct ZoO_knowledge_link *) NULL)
   {
      *links_count -= 1;

      return -1;
   }

   if (*result < (*links_count - 1))
   {
      memmove(
         (void *) (new_p + *result + 1),
         (const void *) (new_p + *result),
         (sizeof(struct ZoO_knowledge_link) * (*links_count - 1 - *result))
      );
   }

   *links = new_p;

   new_p += *result;

   memcpy
   (
      (void *) new_p->sequence,
      (void const *) sequence,
      /* can be zero */
      (sizeof(ZoO_index) * ZoO_SEQUENCE_SIZE)
   );

   new_p->occurrences = 0;
   new_p->targets_count = 0;
   new_p->targets_occurrences = (ZoO_index *) NULL;
   new_p->targets = (ZoO_index *) NULL;

   return 0;
}
