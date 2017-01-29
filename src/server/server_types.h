#ifndef _ZoO_SERVER_SERVER_TYPES_H_
#define _ZoO_SERVER_SERVER_TYPES_H_

#include <mqueue.h>

#include "../core/index.h"

#include "../pipe/pipe_types.h"

struct ZoO_server_message
{
   char type;
   union
   {
      struct ZoO_pipe_names pipe_names;
      ZoO_index pthread_id;
   } data;
};

struct ZoO_server
{
   /* TODO: insert 2 thread barrier. */
   mqd_t mailbox;
   ZoO_index running_threads;
};

#endif
