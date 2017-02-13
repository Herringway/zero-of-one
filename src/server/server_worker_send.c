#include <stdio.h>
#include <string.h>

#include "../error/error.h"

#include "server.h"

int ZoO_server_worker_send_confirm_protocol_version
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   int err;

   err = fprintf(worker->socket_as_file, "!CPV 1\n");

   if (err == 0)
   {
      ZoO_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      ZoO_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

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

   if (err == 0)
   {
      ZoO_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      ZoO_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

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

   if (err == 0)
   {
      ZoO_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      ZoO_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

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

   err = fputs
   (
      "!GR ",
      worker->socket_as_file
   );

   if (err == 0)
   {
      ZoO_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      ZoO_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

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

   if (err == 0)
   {
      ZoO_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      ZoO_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

      return -1;
   }

   err = fputs
   (
      "\n",
      worker->socket_as_file
   );

   if (err == 0)
   {
      ZoO_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }

   return 0;
}
