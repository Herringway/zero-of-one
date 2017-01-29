#include <signal.h>
#include <stdio.h>

#include "../parameters/parameters.h"

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
   struct ZoO_server_worker_parameters worker_params;

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

   ZoO_server_worker_initialize_parameters
   (
      &worker_params,
      &server,
      &msg_buffer,
      &params
   );

   while ((ZoO_SERVER_IS_RUNNING == (char) 1) || (server.running_threads > 0))
   {
      if (ZoO_server_receive_message(&server, &msg_buffer) < 0)
      {
         ZoO_server_no_mq_termination(&server);

         break;
      }

      switch (msg_buffer.type)
      {
         case 'C': /* Client request */
            ZoO_server_add_worker(&server, &worker_params);
            break;

         case 'J': /* Join request */
            ZoO_server_finalize_worker(&server, &msg_buffer);
            break;

         default:
            fprintf
            (
               stderr,
               "[W] Received message with unknown type '%c'.\n",
               msg_buffer.type
            );
            break;
      }
   }

   ZoO_server_finalize(&server);

   return 0;
}
