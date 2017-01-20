#ifndef _ZoO_SERVER_SERVER_TYPES_H_
#define _ZoO_SERVER_SERVER_TYPES_H_

#include <mqueue.h>

#include "../core/index.h"

struct ZoO_server_pipes_data
{
   char request_pipe[255];
   char reply_pipe[255];
};

struct ZoO_server_message
{
   char type;
   union
   {
      struct ZoO_server_pipes_data pipes_name;
      ZoO_index pthread_id;
   } data;
};

struct ZoO_server
{
   mqd_t mailbox;
   ZoO_index running_threads;
};

#endif
