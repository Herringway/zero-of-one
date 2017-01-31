#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/un.h>

#include "server.h"

static int create_socket (int result [const restrict static 1])
{
   const int old_errno = errno;

   errno = 0;
   *result = socket(AF_UNIX, SOCK_STREAM, 0);

   if (*result == -1)
   {
      fprintf
      (
         stderr,
         "[F] Unable to create server socket: %s.\n",
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   errno = old_errno;

   return 0;
}

static int bind_socket
(
   const int socket,
   const char socket_name [const restrict static 1]
)
{
   struct sockaddr_un addr;
   const int old_errno = errno;

   errno = 0;
   memset(&addr, 0, sizeof(struct sockaddr_un));

   addr.sun_family = AF_UNIX;

   /* addr.sun_path == 108. Using 107 ensure null-termination. */
   strncpy(addr.sun_path, socket_name, 107);

   errno = old_errno;

   if
   (
      bind
      (
         socket,
         (const struct sockaddr *) &addr,
         (socklen_t) sizeof(struct sockaddr_un)
      ) != 0
   )
   {
      fprintf
      (
         stderr,
         "[F] Unable to bind server socket to %s: %s.\n",
         socket_name,
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   errno = old_errno;

   return 0;
}

static int set_socket_to_unblocking (const int socket)
{
   int current_flags;
   const int old_errno = errno;

   current_flags = fcntl(socket, F_GETFD);

   if (current_flags == -1)
   {
      fprintf
      (
         stderr,
         "[F] Unable to get server socket properties: %s.\n",
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   /* current_flags = current_flags & (~O_NONBLOCK); */

   current_flags = fcntl(socket, F_SETFD, (current_flags | O_NONBLOCK));

   if (current_flags == -1)
   {
      fprintf
      (
         stderr,
         "[F] Unable to set server socket properties: %s.\n",
         strerror(errno)
      );

      errno = old_errno;

      return -2;
   }

   errno = old_errno;

   return 0;
}

static int set_socket_as_listener (const int socket)
{
   const int old_errno = errno;

   if (listen(socket, ZoO_SERVER_SOCKET_LISTEN_BACKLOG) != 0)
   {
      fprintf
      (
         stderr,
         "[F] Unable to set server socket properties: %s.\n",
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   errno = old_errno;

   return 0;
}

int ZoO_server_socket_open
(
   struct ZoO_server_socket server_socket [const restrict static 1],
   const char socket_name [const restrict static 1]
)
{
   if (create_socket(&(server_socket->file_descriptor)) < 0)
   {
      return -1;
   }

   if (bind_socket(server_socket->file_descriptor, socket_name) < 0)
   {
      close(server_socket->file_descriptor);

      return -1;
   }

   if (set_socket_to_unblocking(server_socket->file_descriptor) < 0)
   {
      close(server_socket->file_descriptor);

      return -1;
   }

   if (set_socket_as_listener(server_socket->file_descriptor) < 0)
   {
      close(server_socket->file_descriptor);

      return -1;
   }

   FD_ZERO(&(server_socket->as_a_set));
   FD_SET(server_socket->file_descriptor, &(server_socket->as_a_set));

   return 0;
}
