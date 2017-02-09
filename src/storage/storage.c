#define _POSIX_C_SOURCE 200809L

#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stdint.h> /* defines SIZE_MAX */
#include <stdio.h>

#include "../error/error.h"

#include "storage.h"

int ZoO_storage_write_line
(
   const char filename [const restrict static 1],
   char line [const restrict static 1],
   size_t const line_size,
   FILE io [const restrict static 1]
)
{
   const int old_errno = errno;
   FILE * file;

   if (filename == (const char *) NULL)
   {
      return 0;
   }

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
         "Could not store line in storage file %s.",
         filename
      );

      fclose(file);

      return -1;
   }

   fclose(file);

   return 0;
}
