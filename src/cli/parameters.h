#ifndef _ZoO_CLI_PARAMETERS_H_
#define _ZoO_CLI_PARAMETERS_H_

#include "parameters_types.h"

char * ZoO_parameters_get_session_name
(
   const struct ZoO_parameters param [const restrict static 1]
);

enum ZoO_invocation_objective ZoO_parameters_initialize
(
   struct ZoO_parameters param [const restrict static 1],
   int const argc,
   const char * argv [const static argc]
);

#endif
