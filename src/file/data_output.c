#define _POSIX_C_SOURCE 200809L

#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stdint.h> /* defines SIZE_MAX */
#include <stdio.h>

#include "error.h"

#include "data_output.h"

int ZoO_data_output_write_line
(
   const char filename [const restrict static 1],
   char line [const restrict static 1],
   size_t const line_size
)
{
   const int old_errno = errno;
   FILE * file;

   file = fopen(filename, "a");

   if (file == (FILE *) NULL)
   {
      ZoO_ERROR
      (
         "Could not open file '%s' in appending mode.",
         filename
      );

      return -1;
   }

   line[line_size - 1] = '\n';

   if
   (
      fwrite
      (
         (const void *) line,
         sizeof(char),
         line_size,
         file
      ) < line_size
   )
   {
      line[line_size - 1] = '\0';

      ZoO_ERROR
      (
         "Could not store line '%s' in %s.",
         line,
         filename
      );

      fclose(file);

      return -1;
   }

   fclose(file);

   return 0;
}
