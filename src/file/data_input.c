#define _POSIX_C_SOURCE 200809L
#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "error.h"

#include "data_input.h"

int ZoO_data_input_open
(
   struct ZoO_data_input di [const static 1],
   const char filename [const restrict static 1]
)
{
   /* prevents di [restrict] */
   ZoO_strings_initialize(&(di->string));

   di->file = fopen(filename, "r");

   if (di->file == (FILE *) NULL)
   {
      ZoO_ERROR
      (
         "Could not open file '%s' in readonly mode.",
         filename
      );

      return -1;
   }

   return 0;
}

int ZoO_data_input_read_line
(
   struct ZoO_data_input di [const static 1],
   ZoO_index const punctuations_count,
   const ZoO_char punctuations [const restrict static punctuations_count]
)
{
   size_t line_size, i, w_start;
   ZoO_char * line;

   /* prevents di [restrict] */
   ZoO_strings_finalize(&(di->string));

   line = (ZoO_char *) NULL;
   line_size = 0;

   /* XXX: assumed compatible with ZoO_char */

   if (getline(&line, &line_size, di->file) < 1)
   {
      free((void *) line);

      return -1;
   }

   line_size = strlen(line);
   line[line_size - 1] = '\0';

   --line_size; /* removed '\n' */

   if
   (
      ZoO_strings_parse
      (
         &(di->string),
         line_size,
         line,
         punctuations_count,
         punctuations
      ) < 0
   )
   {
      free((void *) line);

      return -1;
   }

   free((void *) line);

   return 0;
}

void ZoO_data_input_close (struct ZoO_data_input di [const static 1])
{
   if (di->file != (FILE *) NULL)
   {
      fclose(di->file);

      di->file = (FILE *) NULL;
   }

   /* prevents di [restrict] */
   ZoO_strings_finalize(&(di->string));
}
