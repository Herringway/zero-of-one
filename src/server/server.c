#include <signal.h>
#include <string.h>
#include <stdio.h>

#include "../parameters/parameters.h"

#include "server.h"

int ZoO_server_main
(
   const struct ZoO_parameters params [const restrict static 1]
)
{
   struct ZoO_server server;
   ZoO_index retries;

   if (ZoO_server_set_signal_handlers < 0)
   {
      return -1;
   }

   if (ZoO_server_initialize(&server, params) < 0)
   {
      return -1;
   }

   while (ZoO_server_is_running())
   {
      switch (ZoO_server_wait_for_event(&server))
      {
         case 0: /* Timed out or signal'd. */
            ZoO_server_handle_joining_threads(&server);

            retries = 0;

            break;

         case 1: /* New client attempted connection. */
            ZoO_server_handle_joining_threads(&server);
            (void) ZoO_server_handle_new_connection(&server);

            retries = 0;

            break;

         case -1: /* Something bad happened. */
            retries += 1;

            if (retries == ZoO_SERVER_MAX_RETRIES)
            {
               ZoO_server_finalize(&server);

               return -1;
            }

            break;
      }
   }

   /* Waiting for the threads to join... */
   while (server.workers.currently_running > 0)
   {
      switch (ZoO_server_wait_for_event(&server))
      {
         case 0: /* Timed out. */
         case 1: /* New client attempted connection. */
            ZoO_server_handle_joining_threads(&server);
            break;

         case -1: /* Something bad happened. */
            retries += 1;

            if (retries == ZoO_SERVER_MAX_RETRIES)
            {
               ZoO_server_finalize(&server);

               return -1;
            }
            break;
      }
   }

   ZoO_server_finalize(&server);

   return 0;
}
