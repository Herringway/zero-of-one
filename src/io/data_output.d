module io.data_output;

import core.stdc.errno;
import core.stdc.stdio;
import core.stdc.string;
import std.string;

import io.error;

int ZoO_data_output_write_line
(
   const string filename,
   char* line,
   const size_t line_size
)
{
   const int old_errno = errno;
   FILE * file;

   file = fopen(filename.toStringz, "a");

   if (file == null)
   {
      ZoO_ERROR
      (
         "Could not open file '%s' in appending mode.",
         filename[0..strlen(filename.toStringz)]
      );

      return -1;
   }

   line[line_size - 1] = '\n';

   if
   (
      fwrite
      (
         line,
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
         filename
      );

      fclose(file);

      return -1;
   }

   fclose(file);

   return 0;
}
