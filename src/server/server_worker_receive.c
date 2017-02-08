#include "server.h"


int ZoO_server_worker_receive
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   ssize_t received;

   received =
      getline
      (
         &(worker->buffer),
         &(worker->buffer_capacity),
         worker->socket_as_file
      );

   if (received == -1)
   {
      /* TODO: error message? */

      return -1;
   }

   worker->buffer_length = (size_t) received;

   return 0;
}
