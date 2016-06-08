#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>

/* "POSIX.1  does not require the inclusion of <sys/types.h>" */
/* - man page for setsockopt */
/* #include <sys/types.h> */
#include <sys/socket.h>
#include <sys/time.h>

#include "error.h"

#include "network.h"

static int re_create_socket (struct ZoO_network net [const restrict static 1])
{
   struct timeval timeout;
   const int old_errno = errno;

   errno = 0;
   timeout.tv_sec = ZoO_NETWORK_TIMEOUT;
   timeout.tv_usec = 0;

   if (net->connection != -1)
   {
      close(net->connection);
   }

   net->connection =
      socket
      (
         net->addrinfo->ai_family,
         net->addrinfo->ai_socktype,
         net->addrinfo->ai_protocol
      );

   if (net->connection == -1)
   {
      ZoO_ERROR("Could not create socket: %s.", strerror(errno));

      goto RETURN_FAILED;
   }

   if
   (
      (
         setsockopt
         (
            net->connection,
            SOL_SOCKET,
            SO_RCVTIMEO,
            (const void *) &timeout,
            (socklen_t) sizeof(struct timeval)
         ) < 0
      )
      ||
      (
         setsockopt
         (
            net->connection,
            SOL_SOCKET,
            SO_SNDTIMEO,
            (const void *) &timeout,
            (socklen_t) sizeof(struct timeval)
         ) < 0
      )
   )
   {
      ZoO_ERROR("Could not set timeout on network socket: %s", strerror(errno));

      goto RETURN_FAILED;
   }

   ZoO_S_DEBUG(ZoO_DEBUG_NETWORK, "(Re)connecting to network...");

   if
   (
      connect
      (
         net->connection,
         net->addrinfo->ai_addr,
         net->addrinfo->ai_addrlen
      ) != 0
   )
   {
      ZoO_ERROR("Could not establish connection: %s", strerror(errno));

      goto RETURN_FAILED;
   }

   errno = old_errno;

   return 0;

RETURN_FAILED:
   errno = old_errno;

   return -1;
}

static int reconnect (struct ZoO_network net [const restrict static 1])
{
   const int old_errno = errno;

   memset(net->in, 0, (sizeof(ZoO_char) * 513));
   memset(net->out, 0, (sizeof(ZoO_char) * 513));
   memset(net->buffer, 0, (sizeof(ZoO_char) * 513));

   net->buffer_index = 0;
   net->buffer_remaining = 0;

   if (re_create_socket(net) < 0)
   {
      return -1;
   }

   snprintf(net->out, 512, "USER %s 8 * :%s\r\n", net->user, net->name);

   if (write(net->connection, net->out, strlen(net->out)) < 1)
   {
      goto RETURN_WRITE_FAILED;
   }

   snprintf(net->out, 512, "NICK %s\r\n", net->nick);

   if (write(net->connection, net->out, strlen(net->out)) < 1)
   {
      goto RETURN_WRITE_FAILED;
   }

   net->buffer_remaining = 0;
   net->buffer_index = 0;

   ZoO_S_DEBUG(ZoO_DEBUG_NETWORK, "(Re)connected.");

   errno = old_errno;

   return 0;

RETURN_WRITE_FAILED:
   ZoO_ERROR
   (
      "Unable to write to the network: %s",
      strerror(errno)
   );

   errno = old_errno;

   return -1;
}

int ZoO_network_connect
(
   struct ZoO_network net [const static 1],
   const char host [const restrict static 1],
   const char port [const restrict static 1],
   const char channel [const restrict static 1],
   const char user [const restrict static 1],
   const char name [const restrict static 1],
   const char nick [const restrict static 1]
)
{
   int error;
   struct addrinfo hints;
   const int old_errno = errno;

   net->connection = -1;
   net->channel = channel;
   net->user = user;
   net->name = name;
   net->nick = nick;
   net->buffer_index = 0;
   net->buffer_remaining = 0;

   memset(&hints, 0, sizeof(struct addrinfo));
   memset(net->in, 0, (sizeof(ZoO_char) * 513));
   memset(net->out, 0, (sizeof(ZoO_char) * 513));
   memset(net->buffer, 0, (sizeof(ZoO_char) * 513));

   hints.ai_family = AF_INET;
   hints.ai_socktype = SOCK_STREAM;

   errno = 0;

   error = getaddrinfo(host, port, &hints, &(net->addrinfo));

   if (error != 0)
   {
      if (error == EAI_SYSTEM)
      {
         ZoO_ERROR
         (
            "Could not retrieve server information: %s.",
            strerror(errno)
         );
      }
      else
      {
         ZoO_FATAL
         (
            "Could not retrieve server information: %s.",
            gai_strerror(error)
         );
      }

      errno = old_errno;

      return -1;
   }

   errno = old_errno;

   reconnect(net);

   return 0;
}

static void buffer_msg
(
   struct ZoO_network net [const static 1]
)
{
   ssize_t in_count, i;

   if (net->buffer_remaining > 0)
   {
      in_count = net->buffer_remaining;
      net->buffer_remaining = 0;

      goto PARSE_READ;
   }

READ_MORE:
   in_count = read(net->connection, net->buffer, 512);

   if (in_count <= 0)
   {
      ZoO_ERROR("Could not read from network: %s", strerror(errno));

      while (reconnect(net) < 0)
      {
         ZoO_S_DEBUG
         (
            ZoO_DEBUG_NETWORK,
            "Attempting new connection in 5s."
         );
         sleep(5);
      }

      goto READ_MORE;
   }

PARSE_READ:
   for (i = 0; i < in_count; ++i)
   {
      net->in[net->buffer_index] = net->buffer[i];

      if
      (
         (net->buffer_index > 0)
         && (net->in[net->buffer_index - 1] == '\r')
         && (net->in[net->buffer_index] == '\n')
      )
      {
         net->buffer_remaining = (in_count - (i + 1));
         net->in_length = (net->buffer_index - 1);
         net->buffer_index = 0;

         if (net->buffer_remaining > 0)
         {
            memmove
            (
               (void *) net->buffer,
               (const void *) (net->buffer + (i + 1)),
               net->buffer_remaining
            );
         }

         return;
      }

      net->buffer_index += 1;

      if (net->buffer_index > 512)
      {
         ZoO_S_WARNING("Incoming message is too long. Discarded.");

         net->buffer_index = 0;
         net->buffer_remaining = 0;

         break;
      }
   }

   goto READ_MORE;
}

void handle_ping (struct ZoO_network net [const restrict static 1])
{
   const int old_errno = errno;

   #if ZoO_RANDOMLY_IGNORE_PING == 1
   if ((rand() % 10) < 3)
   {
      ZoO_S_DEBUG(ZoO_DEBUG_NETWORK, "Ping request ignored.");

      return;
   }

   #endif

   #if ZoO_DEBUG_NETWORK_PING == 1
      net->in[net->in_length] = '\0';

      ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET->in] %s", net->in);

      net->in[net->in_length] = '\r';
   #endif

   net->in[1] = 'O';

   errno = 0;

   if (write(net->connection, net->in, (net->in_length + 2)) < 1)
   {
      ZoO_ERROR("Could not reply to PING request: %s", strerror(errno));

      errno = old_errno;

      while (reconnect(net) < 0)
      {
         ZoO_S_DEBUG
         (
            ZoO_DEBUG_NETWORK,
            "Attempting new connection in 5s."
         );
         sleep(5);
      }

      return;
   }

   errno = old_errno;

#if ZoO_DEBUG_NETWORK_PING == 1
   net->in[net->in_length] = '\0';

   ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET->out] %s", net->in);
#endif

}

int ZoO_network_receive
(
   struct ZoO_network net [const restrict static 1],
   size_t msg_offset [const restrict static 1],
   size_t msg_size [const restrict static 1],
   enum ZoO_msg_type type [const restrict static 1]
)
{
   const int old_errno = errno;
   ssize_t cmd, i;

READ_NEW_MSG:
   buffer_msg(net);

   net->in[net->in_length + 2] = '\0';

   /* XXX: doesn't that prevent net [restrict]? */
   if (ZoO_IS_PREFIX("PING", net->in))
   {

      handle_ping(net);

      goto READ_NEW_MSG;
   }

   if (net->in_length == 0)
   {
      goto READ_NEW_MSG;
   }

   net->in[net->in_length] = '\0';

   ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET->in] %s", net->in);

   if (net->in[0] == ':')
   {
      cmd = 0;

      for (i = 1; i < 512; i++)
      {
         if (net->in[i] == ' ')
         {
            cmd = (i + 1);

            break;
         }
      }

      if (ZoO_IS_PREFIX("001", (net->in + cmd)))
      {
         snprintf
         (
            net->out,
            512,
            "JOIN :%s\r\n",
            net->channel
         );

         errno = 0;

         if (write(net->connection, net->out, strlen(net->out)) < 1)
         {
            ZoO_ERROR
            (
               "Could not send JOIN request: %s",
               strerror(errno)
            );

            errno = old_errno;

            if (reconnect(net) < 0)
            {
               return -1;
            }
         }

         errno = old_errno;

         ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET->out] %s", net->out);

         goto READ_NEW_MSG;
      }

      if (ZoO_IS_PREFIX("JOIN", (net->in + cmd)))
      {
         for (i = 1; (i < 512) && (net->in[i] != '!'); ++i)
         {
         }

         if ((i == 512) || (i == 1))
         {
            ZoO_ERROR("Could not find JOIN username: %s", net->in);

            goto READ_NEW_MSG;
         }

         *msg_offset = 1;
         *msg_size = (i - 1);
         net->in[i] = '\0';

         *type = ZoO_JOIN;

         return 0;
      }

      if (ZoO_IS_PREFIX("PRIVMSG", (net->in + cmd)))
      {

         for (; i < 512; i++)
         {
            if (net->in[i] == ':')
            {
               cmd = (i + 1);

               break;
            }
         }

         *msg_offset = cmd;
         *msg_size = (net->in_length - cmd);

         /*net->in[*msg_size - 1] = '\0'; */

         *type = ZoO_PRIVMSG;

         return 0;
      }
   }

   if (ZoO_IS_PREFIX("ERROR", (net->in + cmd)))
   {
      while (reconnect(net) < 0)
      {
         ZoO_S_DEBUG
         (
            ZoO_DEBUG_NETWORK,
            "Attempting new connection in 5s."
         );
         sleep(5);
      }
   }

   goto READ_NEW_MSG;
}

int ZoO_network_send (struct ZoO_network net [const restrict static 1])
{
   int const old_errno = errno;

   snprintf
   (
      net->in,
      512,
      "PRIVMSG %s :%s\r\n",
      net->channel,
      net->out
   );

   errno = 0;

   if (write(net->connection, net->in, strlen(net->in)) < 1)
   {
      ZoO_ERROR
      (
         "Could not send PRIVMSG: %s.",
         strerror(errno)
      );

      errno = old_errno;

      if (reconnect(net) < 0)
      {
         return -2;
      }
      else
      {
         return -1;
      }
   }

   errno = old_errno;

   ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET->out] %s", net->in);

   return 0;
}

void ZoO_network_disconnect (struct ZoO_network net [const restrict static 1])
{
   freeaddrinfo(net->addrinfo);
   close(net->connection);
}

