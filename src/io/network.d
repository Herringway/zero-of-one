module io.network;

import std.string;

import io.network_types;
import io.error;

import pervasive;

import core.stdc.errno;
import core.stdc.stdio;
import core.stdc.string;

import core.sys.posix.sys.time;
import core.sys.posix.unistd;
import core.sys.posix.netdb;

extern(C):

int re_create_socket (ZoO_network* net)
{
   timeval timeout;
   const int old_errno = errno;

   errno = 0;
   timeout.tv_sec = ZoO_NETWORK_TIMEOUT;
   timeout.tv_usec = 0;

   if (net.connection != -1)
   {
      close(net.connection);
   }

   net.connection =
      socket
      (
         net.addrinfo.ai_family,
         net.addrinfo.ai_socktype,
         net.addrinfo.ai_protocol
      );

   if (net.connection == -1)
   {
      ZoO_ERROR("Could not create socket: %s.", strerror(errno));

      goto RETURN_FAILED;
   }

   if
   (
      (
         setsockopt
         (
            net.connection,
            SOL_SOCKET,
            SO_RCVTIMEO,
            &timeout,
            timeval.sizeof
         ) < 0
      )
      ||
      (
         setsockopt
         (
            net.connection,
            SOL_SOCKET,
            SO_SNDTIMEO,
            &timeout,
            timeval.sizeof
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
         net.connection,
         net.addrinfo.ai_addr,
         net.addrinfo.ai_addrlen
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

int reconnect (ZoO_network* net)
{
   const int old_errno = errno;

   memset(net.in_.ptr, 0, (ZoO_char.sizeof * 513));
   memset(net.out_.ptr, 0, (ZoO_char.sizeof * 513));
   memset(net.buffer.ptr, 0, (ZoO_char.sizeof * 513));

   net.buffer_index = 0;
   net.buffer_remaining = 0;

   if (re_create_socket(net) < 0)
   {
      return -1;
   }

   snprintf(net.out_.ptr, 512, "USER %s 8 * :%s\r\n", net.user, net.name);

   if (write(net.connection, net.out_.ptr, strlen(net.out_.ptr)) < 1)
   {
      goto RETURN_WRITE_FAILED;
   }

   snprintf(net.out_.ptr, 512, "NICK %s\r\n", net.nick);

   if (write(net.connection, net.out_.ptr, strlen(net.out_.ptr)) < 1)
   {
      goto RETURN_WRITE_FAILED;
   }

   net.buffer_remaining = 0;
   net.buffer_index = 0;

   ZoO_S_DEBUG(ZoO_DEBUG_NETWORK, "(Re)connected.");

   errno = old_errno;

   return 0;

RETURN_WRITE_FAILED:
   ZoO_ERROR
   (
      "Unable to write to the network: %s",
      strerror(errno).fromStringz
   );

   errno = old_errno;

   return -1;
}

int ZoO_network_connect
(
   ZoO_network* net,
   const(char)* host,
   const(char)* port,
   const(char)* channel,
   const(char)* user,
   const(char)* name,
   const(char)* nick
)
{
   int error;
   addrinfo hints;
   const int old_errno = errno;

   net.connection = -1;
   net.channel = channel;
   net.user = user;
   net.name = name;
   net.nick = nick;
   net.buffer_index = 0;
   net.buffer_remaining = 0;

   memset(&hints, 0, addrinfo.sizeof);
   memset(net.in_.ptr, 0, (ZoO_char.sizeof * 513));
   memset(net.out_.ptr, 0, (ZoO_char.sizeof * 513));
   memset(net.buffer.ptr, 0, (ZoO_char.sizeof * 513));

   hints.ai_family = AF_INET;
   hints.ai_socktype = SOCK_STREAM;

   errno = 0;

   error = getaddrinfo(host, port, &hints, &(net.addrinfo));

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

void buffer_msg
(
   ZoO_network* net
)
{
   ssize_t in_count, i;

   if (net.buffer_remaining > 0)
   {
      in_count = net.buffer_remaining;
      net.buffer_remaining = 0;

      goto PARSE_READ;
   }

READ_MORE:
   in_count = read(net.connection, net.buffer.ptr, 512);

   if (in_count <= 0)
   {
      ZoO_ERROR("Could not read from network: %s", strerror(errno).fromStringz);

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
      net.in_[net.buffer_index] = net.buffer[i];

      if
      (
         (net.buffer_index > 0)
         && (net.in_[net.buffer_index - 1] == '\r')
         && (net.in_[net.buffer_index] == '\n')
      )
      {
         net.buffer_remaining = (in_count - (i + 1));
         net.in_length = (net.buffer_index - 1);
         net.buffer_index = 0;

         if (net.buffer_remaining > 0)
         {
            memmove
            (
               net.buffer.ptr,
               net.buffer.ptr + (i + 1),
               net.buffer_remaining
            );
         }

         return;
      }

      net.buffer_index += 1;

      if (net.buffer_index > 512)
      {
         ZoO_S_WARNING("Incoming message is too long. Discarded.");

         net.buffer_index = 0;
         net.buffer_remaining = 0;

         break;
      }
   }

   goto READ_MORE;
}


void handle_ping (ZoO_network* net)
{
   const int old_errno = errno;

   static if (ZoO_RANDOMLY_IGNORE_PING == 1) {
   if ((rand() % 10) < 3)
   {
      ZoO_S_DEBUG(ZoO_DEBUG_NETWORK, "Ping request ignored.");

      return;
   }

   }

   static if(ZoO_DEBUG_NETWORK_PING == 1) {
      net.in_[net.in_length] = '\0';

      ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET.in] %s", net.in_.fromStringz);

      net.in_[net.in_length] = '\r';
   }

   net.in_[1] = 'O';

   errno = 0;

   if (write(net.connection, net.in_.ptr, (net.in_length + 2)) < 1)
   {
      ZoO_ERROR("Could not reply to PING request: %s", strerror(errno).fromStringz);

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

   static if (ZoO_DEBUG_NETWORK_PING == 1) {
      net.in_[net.in_length] = '\0';

      ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET.out] %s", net.in_.fromStringz);
   }

}

int ZoO_network_receive
(
   ZoO_network* net,
   size_t* msg_offset,
   size_t* msg_size,
   ZoO_msg_type* type
)
{
   const int old_errno = errno;
   ssize_t cmd, i;

READ_NEW_MSG:
   buffer_msg(net);

   net.in_[net.in_length + 2] = '\0';

   /* XXX: doesn't that prevent net [restrict]? */
   if (strncmp("PING", net.in_.ptr, "PING".length) == 0)
   {

      handle_ping(net);

      goto READ_NEW_MSG;
   }

   if (net.in_length == 0)
   {
      goto READ_NEW_MSG;
   }

   net.in_[net.in_length] = '\0';

   ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET.in] %s", net.in_.ptr.fromStringz);

   if (net.in_[0] == ':')
   {
      cmd = 0;

      for (i = 1; i < 512; i++)
      {
         if (net.in_[i] == ' ')
         {
            cmd = (i + 1);

            break;
         }
      }

      if (strncmp("001", (net.in_.ptr + cmd), strlen("001")) == 0)
      {
         snprintf
         (
            net.out_.ptr,
            512,
            "JOIN :%s\r\n",
            net.channel
         );

         errno = 0;

         if (write(net.connection, net.out_.ptr, strlen(net.out_.ptr)) < 1)
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

         ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET.out] %s", net.out_.ptr.fromStringz);

         goto READ_NEW_MSG;
      }

      if (strncmp("JOIN", (net.in_.ptr + cmd), strlen("JOIN")) == 0)
      {
         for (i = 1; (i < 512) && (net.in_[i] != '!'); ++i)
         {
         }

         if ((i == 512) || (i == 1))
         {
            ZoO_ERROR("Could not find JOIN username: %s", net.in_);

            goto READ_NEW_MSG;
         }

         *msg_offset = 1;
         *msg_size = (i - 1);
         net.in_[i] = '\0';

         *type = ZoO_msg_type.ZoO_JOIN;

         return 0;
      }

      if (strncmp("PRIVMSG", (net.in_.ptr + cmd), strlen("PRIVMSG")) == 0)
      {

         for (; i < 512; i++)
         {
            if (net.in_[i] == ':')
            {
               cmd = (i + 1);

               break;
            }
         }

         *msg_offset = cmd;
         *msg_size = (net.in_length - cmd);

         /*net.in[*msg_size - 1] = '\0'; */

         *type = ZoO_msg_type.ZoO_PRIVMSG;

         return 0;
      }
   }

   if (strncmp("ERROR", (net.in_.ptr + cmd), strlen("ERROR")) == 0)
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

int ZoO_network_send (ZoO_network* net)
{
   const int old_errno = errno;

   if (strncmp("\001action".ptr, net.out_.ptr, strlen("\001action")) == 0)
   {

      net.out_[1] = 'A';
      net.out_[2] = 'C';
      net.out_[3] = 'T';
      net.out_[4] = 'I';
      net.out_[5] = 'O';
      net.out_[6] = 'N';

      snprintf
      (
         net.in_.ptr,
         512,
         "PRIVMSG %s :%s\001\r\n",
         net.channel,
         net.out_.ptr
      );
   }
   else
   {
      snprintf
      (
         net.in_.ptr,
         512,
         "PRIVMSG %s :%s\r\n",
         net.channel,
         net.out_.ptr
      );
   }

   errno = 0;

   if (write(net.connection, net.in_.ptr, strlen(net.in_.ptr)) < 1)
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

   ZoO_DEBUG(ZoO_DEBUG_NETWORK, "[NET.out] %s", net.in_[0..net.in_length]);

   return 0;
}

void ZoO_network_disconnect (ZoO_network* net)
{
   freeaddrinfo(net.addrinfo);
   close(net.connection);
}
