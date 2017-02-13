#include <sys/select.h>

#include <errno.h>
#include <stdio.h>
#include <string.h>

#include "../error/error.h"

#include "server.h"

int ZoO_server_wait_for_event
(
   struct ZoO_server server [const static 1]
)
{
   int ready_fds;
   const int old_errno = errno;
   fd_set ready_to_read;

   ready_to_read = server->socket.as_a_set;

   /* call to select may alter timeout */
   memset((void *) &(server->socket.timeout), 0, sizeof(struct timeval));

   server->socket.timeout.tv_sec = ZoO_SERVER_SOCKET_ACCEPT_TIMEOUT_SEC;

   errno = 0;

   ready_fds = select
   (
      (server->socket.file_descriptor + 1),
      &ready_to_read,
      (fd_set *) NULL,
      (fd_set *) NULL,
      &(server->socket.timeout)
   );

   ZoO_DEBUG(stderr, 1, "SELECT returned: %i, errno is %i.", ready_fds, errno);

   if (errno == EINTR)
   {
      ready_fds = 0;
   }

   if (ready_fds == -1)
   {
      ZoO_FATAL
      (
         stderr,
         "Unable to wait on server socket: %s.",
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   errno = old_errno;

   return ready_fds;
}
