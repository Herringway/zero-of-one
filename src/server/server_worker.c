#include "worker.h"

void ZoO_worker_initialize_parameters
(
   struct ZoO_worker_parameters worker_params;
   const struct ZoO_server_message msg_buffer [const restrict static 1],
   const struct ZoO_parameters params [const restrict static 1]
)
{
   worker_params->thread_id = 0;
   pthread_barrier_t * barrier;
   mqd_t * server_mailbox;
   const struct ZoO_pipe_names * pipe_names;

   /* Program data */
   ZoO_index markov_order;
   struct ZoO_knowledge * k;
   const char * storage_filename;

   /* TODO */
}
