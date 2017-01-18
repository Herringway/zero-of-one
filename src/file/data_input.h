#ifndef _ZoO_IO_DATA_INPUT_H_
#define _ZoO_IO_DATA_INPUT_H_

#include "data_input_types.h"

int ZoO_data_input_open
(
   struct ZoO_data_input di [const static 1],
   const char filename [const restrict static 1]
);

int ZoO_data_input_read_line
(
   struct ZoO_data_input di [const static 1],
   ZoO_index const punctuations_count,
   const ZoO_char punctuations [const restrict static punctuations_count]
);

void ZoO_data_input_close (struct ZoO_data_input di [const static 1]);

#endif
