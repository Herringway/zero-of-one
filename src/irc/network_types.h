#ifndef _ZoO_IO_NETWORK_TYPES_H_
#define _ZoO_IO_NETWORK_TYPES_H_

#define POSIX_C_SOURCE

#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>

#include "../pervasive.h"

enum ZoO_msg_type
{
   ZoO_PRIVMSG,
   ZoO_JOIN
};

struct ZoO_network
{
   size_t buffer_index;
   size_t buffer_remaining;
   size_t in_length;
   struct addrinfo * addrinfo;
   ZoO_char buffer [513];
   ZoO_char in [513];
   ZoO_char out [513];
   int connection;
   const char * restrict channel;
   const char * restrict user;
   const char * restrict name;
   const char * restrict nick;
};

#endif
