#include <signal.h>

#include "../cli/parameters.h"

#include "server.h"

volatile char ZoO_SERVER_IS_RUNNING = (char) 1;

static void request_termination (int const signo)
{
   if ((signo == SIGINT) || (signo == SIGTERM))
   {
      ZoO_SERVER_IS_RUNNING = (char) 0;
   }
}

int ZoO_server_main (const struct ZoO_parameters params)
{
   struct ZoO_server server;
   struct ZoO_server_message msg_buffer;

   if
   (
      ZoO_server_initialize
      (
         &server,
         ZoO_parameters_get_session_name(&params)
      ) < 0
   )
   {
      return -1;
   }

   while ((ZoO_SERVER_IS_RUNNING == (char) 1) || (server.running_threads > 0))
   {
      if (ZoO_server_receive_message(&server, &msg_buffer) < 0)
      {
         ZoO_server_no_mq_termination(&server);

         break;
      }

      switch (msg_buffer.type)
      {
         case 'C':
            ZoO_server_new_client(&server, &msg_buffer);

         case 'J':
            ZoO_server_join_thread(&server, &msg_buffer);

         default:
            break;
      }
   }

   ZoO_server_finalize(&server);

   return 0;
}
