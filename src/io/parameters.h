#ifndef _ZoO_IO_PARAMETERS_H_
#define _ZoO_IO_PARAMETERS_H_

#include "parameters_types.h"

int ZoO_parameters_initialize
(
   struct ZoO_parameters param [const static 1],
   int const argc,
   const char * argv [const static argc]
);

#endif
