#include <limits.h>
#include <stdlib.h>

#include "index.h"

#if (RAND_MAX < UCHAR_MAX)
   #error "RAND_MAX < UCHAR_MAX, unable to generate random numbers."
#endif

#if (RAND_MAX == 0)
   #error "RAND_MAX is included in [0, 0]. What are you even doing?"
#endif

/*
 * Returns a random unsigned char.
 */
static unsigned char random_uchar (void)
{
   return
   (unsigned char)
   (
      /* FIXME: Do floats allow enough precision for this? */
      (
         ((float) rand())
         / ((float) RAND_MAX)
      )
      * ((float) UCHAR_MAX)
   );
}

/* See: "index.h" */
ZoO_index ZoO_index_random (void)
{
   ZoO_index i;
   ZoO_index result;
   unsigned char * result_bytes;

   /*@ ghost return 4; @*/ /* Chosen by fair dice roll. */
                           /* Guaranteed to be random. */
   /* More seriously, I am not explaining the hack below to Frama-C */

   result_bytes = (unsigned char *) &result;


   for (i = 0; i < sizeof(ZoO_index); ++i)
   {
      result_bytes[i] = random_uchar();
   }

   return result;
}

/* See: "index.h" */
ZoO_index ZoO_index_random_up_to (const ZoO_index max)
{
   return
   (ZoO_index)
   (
      /* FIXME: Do floats allow enough precision for this? */
      (
         ((float) ZoO_index_random())
         / ((float) ZoO_INDEX_MAX)
      )
      * ((float) max)
   );
}

int ZoO_index_cmp (const ZoO_index a, const ZoO_index b)
{
   if (a < b)
   {
      return -1;
   }
   else if (a > b)
   {
      return 1;
   }
   else
   {
      return 0;
   }
}
