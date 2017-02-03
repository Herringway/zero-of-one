#ifndef _ZoO_CLI_PARAMETERS_TYPES_H_
#define _ZoO_CLI_PARAMETERS_TYPES_H_

#include "../core/index_types.h"

enum ZoO_invocation_objective
{
   ZoO_PRINTS_HELP,
   ZoO_CLEANS_UP,
   ZoO_RUNS
};

struct ZoO_parameters
{
   const char * restrict session;
   ZoO_index markov_order;
   const char * restrict storage;
};

#endif
