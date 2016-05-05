#ifndef _ZoO_IO_NETWORK_TYPES_H_
#define _ZoO_IO_NETWORK_TYPES_H_

#define POSIX_C_SOURCE

#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>

#include "../pervasive.h"

struct ZoO_network
{
   size_t buffer_index;
   size_t buffer_remaining;
   struct addrinfo * addrinfo;
   ZoO_char buffer [513];
   ZoO_char msg [513];
   int connection;
   const char * restrict channel;
   const char * restrict user;
   const char * restrict name;
   const char * restrict nick;
};

#endif
