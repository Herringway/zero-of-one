module core.sequence;

import core.stdc.stdlib;
import core.stdc.string;

import core.knowledge_types;

import tool.sorted_list;

import pervasive;

extern(C):

int cmp_seq_link
(
   const void* a,
   const void* b,
   const void* other
)
{
   ZoO_index j;
   const ZoO_index* sequence = cast(const ZoO_index *) a;
   const ZoO_knowledge_link* link = cast(const ZoO_knowledge_link *) b;

   for (j = 0; j < ZoO_SEQUENCE_SIZE; ++j)
   {
      if (sequence[j] < link.sequence[j])
      {
         return -1;
      }
      else if (sequence[j] > link.sequence[j])
      {
         return 1;
      }
   }

   return 0;
}

int ZoO_knowledge_find_link
(
   const ZoO_index links_count,
   ZoO_knowledge_link* links,
   const ZoO_index* sequence,
   ZoO_index* result
)
{
   return
      ZoO_sorted_list_index_of
      (
         links_count,
         cast(const void*) links,
         cast(const void*) sequence,
         ZoO_knowledge_link.sizeof,
         &cmp_seq_link,
         cast(const void*) null,
         result
      );
}

int ZoO_knowledge_get_link
(
   ZoO_index* links_count,
   ZoO_knowledge_link** links,
   const ZoO_index* sequence,
   ZoO_index* result
)
{
   ZoO_knowledge_link* new_p;

   if
   (
      ZoO_sorted_list_index_of
      (
         *links_count,
         cast(const void*) *links,
         cast(const void*) sequence,
         ZoO_knowledge_link.sizeof,
         &cmp_seq_link,
         cast(const void*) null,
         result
      ) == 0
   )
   {
      return 0;
   }

   *links_count += 1;

   new_p =
      cast(ZoO_knowledge_link *) realloc
      (
         cast(void *) *links,
         (ZoO_knowledge_link.sizeof * (*links_count))
      );

   if (new_p == cast(ZoO_knowledge_link *) null)
   {
      *links_count -= 1;

      return -1;
   }

   if (*result < (*links_count - 1))
   {
      memmove(
         cast(void *) (new_p + *result + 1),
         cast(const void *) (new_p + *result),
         (ZoO_knowledge_link.sizeof * (*links_count - 1 - *result))
      );
   }

   *links = new_p;

   new_p += *result;

   memcpy
   (
      cast(void *) new_p.sequence,
      cast(const void*) sequence,
      /* can be zero */
      (ZoO_index.sizeof * ZoO_SEQUENCE_SIZE)
   );

   new_p.occurrences = 0;
   new_p.targets_count = 0;
   new_p.targets_occurrences = cast(ZoO_index *) null;
   new_p.targets = cast(ZoO_index *) null;

   return 0;
}