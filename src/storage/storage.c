#define _POSIX_C_SOURCE 200809L

#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stdint.h> /* defines SIZE_MAX */
#include <stdio.h>

#include "../pipe/pipe.h"

#include "storage.h"

int ZoO_storage_write_line
(
   const char filename [const restrict static 1],
   char line [const restrict static 1],
   size_t const line_size,
   const struct ZoO_pipe io [const restrict static 1]
)
{
   const int old_errno = errno;
   FILE * file;

   file = fopen(filename, "a");

   if (file == (FILE *) NULL)
   {
      ZoO_ERROR
      (
         io,
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
         io,
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
