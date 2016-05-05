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

static int reconnect (struct ZoO_network net [const restrict static 1])
{
   struct timeval timeout;
   int old_errno = errno;

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
      ZoO_FATAL
      (
         "Could not create socket: %s.",
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   errno = 0;

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

      errno = old_errno;

      return -1;
   }

   errno = old_errno;

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
      ZoO_ERROR
      (
         "Unable to connect to the network: %s",
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   errno = old_errno;

   snprintf
   (
      net->msg,
      512,
      "USER %s 8 * :%s\r\n",
      net->user,
      net->name
   );

   errno = 0;

   if (write(net->connection, net->msg, strlen(net->msg)) < 1)
   {
      ZoO_ERROR
      (
         "Unable to write to the network: %s",
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   snprintf
   (
      net->msg,
      512,
      "NICK %s\r\n",
      net->nick
   );

   errno = 0;

   if (write(net->connection, net->msg, strlen(net->msg)) < 1)
   {
      ZoO_ERROR
      (
         "Unable to write to the network: %s",
         strerror(errno)
      );

      errno = old_errno;

      return -1;
   }

   errno = old_errno;

   net->buffer_remaining = 0;
   net->buffer_index = 0;
   ZoO_S_DEBUG(ZoO_DEBUG_NETWORK, "(Re)connected.");

   return 0;
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
   memset(net->msg, 0, (sizeof(ZoO_char) * 513));

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

   errno = 0;


   reconnect(net);

   return 0;
}

int ZoO_network_receive
(
   struct ZoO_network net [const restrict static 1],
   size_t msg_offset [const restrict static 1],
   size_t msg_size [const restrict static 1]
)
{
   int old_errno;
   ssize_t in_count, in_index, msg_index, cmd;

   old_errno = errno;

   for (;;)
   {
      msg_index = 0;

      errno = 0;

      while
      (
         (
            (in_count =
               read(
                  net->connection,
                  (net->buffer + net->buffer_index),
                  (512 - net->buffer_index)
               )
            ) > 0
         )
      )
      {
         net->buffer_remaining += in_count;

         for
         (
            in_index = 0;
            in_index < net->buffer_remaining;
            ++in_index
         )
         {
            net->msg[msg_index] = net->buffer[net->buffer_index + in_index];

            if
            (
               (msg_index == 511)
               ||
               (
                  (msg_index > 0)
                  && (net->msg[msg_index - 1] == '\r')
                  && (net->msg[msg_index] == '\n')
               )
            )
            {
               net->msg[msg_index + 1] = '\0';


               if (net->buffer_index != net->buffer_remaining)
               {
                  memmove
                  (
                     net->buffer,
                     (net->buffer + net->buffer_index),
                     (size_t) net->buffer_remaining
                  );

                  net->buffer_index = 0;
               }

               net->buffer_remaining -= (in_index + 1);

               errno = old_errno;

               goto READ_MSG;
            }

            ++msg_index;
         }

         net->buffer_remaining = 0;
         net->buffer_index = 0;

         errno = 0;
      }

      ZoO_ERROR
      (
         "Something went wrong while trying to read from the network: %s.",
         strerror(errno)
      );

      errno = old_errno;

      if (reconnect(net) < 0)
      {
         return -1;
      }

      continue;

      READ_MSG:

      ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET->in] %s\n", net->msg);

      /* XXX: doesn't that prevent net [restrict]? */
      if (ZoO_IS_PREFIX("PING", net->msg))
      {
         errno = 0;

         net->msg[1] = 'O';

         if (write(net->connection, net->msg, strlen(net->msg)) < 1)
         {
            ZoO_ERROR("Could not reply to PING request: %s", strerror(errno));

            errno = old_errno;

            if (reconnect(net) < 0)
            {
               return -1;
            }

            continue;
         }

         ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET->out] %s\n", net->msg);

         errno = old_errno;
      }
      else if (net->msg[0] == ':')
      {
         cmd = 0;

         for (in_index = 1; in_index < 512; in_index++)
         {
            if (net->msg[in_index] == ' ')
            {
               cmd = (in_index + 1);

               break;
            }
         }

         if (cmd == 0)
         {
            continue;
         }

         if (ZoO_IS_PREFIX("001", (net->msg + cmd)))
         {
            snprintf
            (
               net->msg,
               512,
               "JOIN :%s\r\n",
               net->channel
            );

            errno = 0;

            if (write(net->connection, net->msg, strlen(net->msg)) < 1)
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

            ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET->out] %s", net->msg);

            continue;
         }

         if (ZoO_IS_PREFIX("PRIVMSG", (net->msg + cmd)))
         {
            for (; in_index < 512; in_index++)
            {
               if (net->msg[in_index] == ':')
               {
                  cmd = (in_index + 1);

                  break;
               }
            }

            *msg_offset = cmd;
            *msg_size = (msg_index - *msg_offset - 1);

            /*net->msg[*msg_size - 1] = '\0'; */

            return 0;
         }
      }
   }
}

int ZoO_network_send (struct ZoO_network net [const restrict static 1])
{
   int const old_errno = errno;

   snprintf
   (
      net->buffer,
      512,
      "PRIVMSG %s :%s\r\n",
      net->channel,
      net->msg
   );

   errno = 0;

   if (write(net->connection, net->buffer, strlen(net->buffer)) < 1)
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

   ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET->out] %s", net->buffer);

   return 0;
}

void ZoO_network_disconnect (struct ZoO_network net [const restrict static 1])
{
   freeaddrinfo(net->addrinfo);
   close(net->connection);
}

