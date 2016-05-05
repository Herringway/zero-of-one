#ifndef _ZoO_IO_NETWORK_H_
#define _ZoO_IO_NETWORK_H_
#include "network_types.h"

int ZoO_network_connect
(
   struct ZoO_network net [const static 1],
   const char host [const restrict static 1],
   const char port [const restrict static 1],
   const char channel [const restrict static 1],
   const char user [const restrict static 1],
   const char name [const restrict static 1],
   const char nick [const restrict static 1]
);

int ZoO_network_receive
(
   struct ZoO_network net [const static 1],
   size_t msg_offset [const restrict static 1],
   size_t msg_size [const restrict static 1]
);

int ZoO_network_send (struct ZoO_network net [const restrict static 1]);

void ZoO_network_disconnect (struct ZoO_network net [const restrict static 1]);

#endif
