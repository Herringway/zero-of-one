#ifndef _ZoO_STORAGE_STORAGE_H_
#define _ZoO_STORAGE_STORAGE_H_

#include "../pipe/pipe_types.h"

int ZoO_storage_write_line
(
   const char filename [const restrict static 1],
   char line [const restrict static 1],
   size_t const line_size,
   const struct ZoO_pipe io [const restrict static 1]
);

#endif
