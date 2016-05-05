#ifndef _ZoO_IO_DATA_INPUT_TYPES_H_
#define _ZoO_IO_DATA_INPUT_TYPES_H_

#include <stdio.h>

#include "../pervasive.h"

#include "../tool/strings.h"

struct ZoO_data_input
{
   FILE * restrict file;
   struct ZoO_strings string;
};

#endif
