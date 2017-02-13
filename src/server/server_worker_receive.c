#include <stdio.h>
#include <string.h>
#include <errno.h>

#include "../error/error.h"

#include "server.h"

int ZoO_server_worker_receive
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   const int old_errno = errno;
   ssize_t received;

   errno = 0;

   received =
      getline
      (
         &(worker->buffer),
         &(worker->buffer_capacity),
         worker->socket_as_file
      );

   if (received == -1)
   {
      ZoO_ERROR
      (
         stderr,
         "Thread could not receive from socket: %s.",
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   errno = old_errno;

   worker->buffer_length = (size_t) received;

   return 0;
}
