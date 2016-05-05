#ifndef _ZoO_CORE_STATE_TYPES_H_
#define _ZoO_CORE_STATE_TYPES_H_

#include "../io/parameters_types.h"
#include "../io/network_types.h"

#include "knowledge_types.h"

struct ZoO_state
{
   struct ZoO_parameters param;
   struct ZoO_knowledge knowledge;
   struct ZoO_network network;
};

#endif
