#ifndef _ZoO_STORAGE_STORAGE_H_
#define _ZoO_STORAGE_STORAGE_H_

#include <stdio.h>

int ZoO_storage_write_line
(
   const char filename [const restrict static 1],
   char line [const restrict static 1],
   size_t const line_size,
   FILE io [const restrict static 1]
);

#endif
