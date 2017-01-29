#ifndef _ZoO_WORKER_WORKER_TYPES_H_
#define _ZoO_WORKER_WORKER_TYPES_H_

#include <mqueue.h>

#include "../core/index_types.h"

#include "../pipes/pipes_types.h"

#include "../knowledge/knowledge_types.h"


struct ZoO_worker_parameters
{
   /* Communication data */
   ZoO_index thread_id;
   pthread_barrier_t * barrier;
   mqd_t * server_mailbox;
   const struct ZoO_pipe_names * pipe_names;

   /* Program data */
   ZoO_index markov_order;
   struct ZoO_knowledge * k;
   const char * storage_filename;
};

#endif
