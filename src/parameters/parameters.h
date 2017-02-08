#ifndef _ZoO_CLI_PARAMETERS_H_
#define _ZoO_CLI_PARAMETERS_H_

#include "parameters_types.h"

const char * ZoO_parameters_get_session_name
(
   const struct ZoO_parameters param [const restrict static 1]
);

ZoO_index ZoO_parameters_get_markov_order
(
   const struct ZoO_parameters param [const restrict static 1]
);

const char * ZoO_parameters_get_storage_filename
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
