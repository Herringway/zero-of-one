#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "server.h"

static int initialize
(
   struct ZoO_server_worker worker [const restrict static 1],
   void * input
)
{
   memcpy
   (
      (void *) &(worker->params),
      (const void *) input,
      sizeof(struct ZoO_server_thread_parameters)
   );

   pthread_barrier_wait(&(worker->params.thread_collection->barrier));

   worker->buffer = (char *) NULL;
   worker->buffer_capacity = 0;
   worker->buffer_length = 0;

   worker->sequence_buffer = (ZoO_index *) NULL;
   worker->sequence_buffer_capacity = 0;
   worker->sequence_buffer_length = 0;

   worker->socket_as_file = fdopen(worker->params.socket, "w+");

   if (worker->socket_as_file == (FILE *) NULL)
   {
      /* TODO: error message? */
      return -1;
   }

   return 0;
}

static void finalize
(
   struct ZoO_server_worker worker [const restrict static 1]
)
{
   if (worker->socket_as_file != (FILE *) NULL)
   {
      fclose(worker->socket_as_file);

      worker->socket_as_file = NULL;
   }

   if (worker->buffer != (char *) NULL)
   {
      free((void *) worker->buffer);

      worker->buffer = (char *) NULL;
   }

   worker->buffer_capacity = 0;
   worker->buffer_length = 0;

   pthread_mutex_lock(&(worker->params.thread_collection->mutex));

   worker->params.thread_collection->threads[worker->params.thread_id].state =
      ZoO_SERVER_JOINING_THREAD;

   pthread_mutex_unlock(&(worker->params.thread_collection->mutex));
}

void * ZoO_server_worker_main (void * input)
{
   struct ZoO_server_worker worker;

   initialize(&worker, input);

   while (ZoO_server_is_running())
   {
      if (ZoO_server_worker_receive(&worker) < 0)
      {
         break;
      }

      if (ZoO_server_worker_handle_request(&worker) < 0)
      {
         break;
      }
   }

   finalize(&worker);

   return NULL;
}
