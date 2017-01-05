#include "./sorted_list.h"

int ZoO_sorted_list_index_of
(
   ZoO_index const list_length,
   const void * const sorted_list,
   const void * const elem,
   size_t const type_size,
   int (*compare) (const void *, const void *, const void *),
   const void * const other,
   ZoO_index result [const restrict static 1]
)
{
   int cmp;
   ZoO_index i, current_min, current_max;
   const char * sorted_list_access;

   sorted_list_access = (char *) sorted_list;

   /* This is a binary search. */

   if (list_length == 0)
   {
      *result = 0;

      return -1;
   }

   current_min = 0;

   current_max = (list_length - 1);

   for (;;)
   {
      /* FIXME: overflow-safe? */
      /* No: (and (> current_min (/ Max 2)) (> current_max (/ Max 2))) */
      i = ((current_min + current_max) / 2);

      if (i == list_length)
      {
         /* FIXME: I don't see how this one can be true */
         *result = list_length;

         return -1;
      }

      cmp = compare(elem, (sorted_list_access + (i * type_size)), other);

      if (cmp > 0)
      {
         if ((current_min > current_max))
         {
            *result = (i + 1);

            return -1;
         }

         /* FIXME: overflow-safe? */
         current_min = (i + 1);
      }
      else if (cmp < 0)
      {
         if ((current_min > current_max) || (i == 0))
         {
            *result = i;

            return -1;
         }

         /* overflow-safe */
         current_max = (i - 1);
      }
      else
      {
         *result = i;

         return 0;
      }
   }
}
