module io.data_output;

import core.stdc.errno;
import core.stdc.stdio;
import core.stdc.string;

import io.error;

extern(C):

int ZoO_data_output_write_line
(
   const char* filename,
   char* line,
   const size_t line_size
)
{
   const int old_errno = errno;
   FILE * file;

   file = fopen(filename, "a");

   if (file == cast(FILE *)null)
   {
      ZoO_ERROR
      (
         "Could not open file '%s' in appending mode.",
         filename[0..strlen(filename)]
      );

      return -1;
   }

   line[line_size - 1] = '\n';

   if
   (
      fwrite
      (
         cast(const void *) line,
         char.sizeof,
         line_size,
         file
      ) < line_size
   )
   {
      line[line_size - 1] = '\0';

      ZoO_ERROR
      (
         "Could not store line '%s' in %s.",
         line[0..strlen(line)],
         filename[0..strlen(filename)]
      );

      fclose(file);

      return -1;
   }

   fclose(file);

   return 0;
}
