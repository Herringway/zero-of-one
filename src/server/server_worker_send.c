#include "../pervasive.h"

#include "server.h"

int ZoO_server_worker_send_confirm_protocol_version
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   int err;

   err = fprintf(worker->socket_as_file, "!CPV 1\n");

   if (err <= 0)
   {
      /* TODO: error message? */

      return -1;
   }

   return 0;
}

int ZoO_server_worker_send_positive
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   int err;

   err = fprintf(worker->socket_as_file, "!P\n");

   if (err <= 0)
   {
      /* TODO: error message? */

      return -1;
   }

   return 0;
}

int ZoO_server_worker_send_negative
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   int err;

   err = fprintf(worker->socket_as_file, "!N\n");

   if (err <= 0)
   {
      /* TODO: error message? */

      return -1;
   }

   return 0;
}

int ZoO_server_worker_send_generated_reply
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   int err;

   /* TODO */
   err = fputs
   (
      "!GR ",
      worker->socket_as_file
   );

   if (err <= 0)
   {
      /* TODO: error message? */

      return -1;
   }

   err =
      fwrite
      (
         worker->buffer,
         sizeof(ZoO_char),
         worker->buffer_length,
         worker->socket_as_file
      );

   err = fputs
   (
      "\n",
      worker->socket_as_file
   );

   if (err <= 0)
   {
      /* TODO: error message? */

      return -1;
   }

   return 0;
}
