#ifndef _ZoO_SERVER_SERVER_TYPES_H_
#define _ZoO_SERVER_SERVER_TYPES_H_

#include <sys/time.h>

#ifndef ZoO_RUNNING_FRAMA_C
   #include <pthread.h>
#endif

#include "../core/index_types.h"

#include "../knowledge/knowledge_types.h"

#include "../parameters/parameters_types.h"

#include "../pipe/pipe_types.h"

#define ZoO_SERVER_MAX_RETRIES 10
#define ZoO_SERVER_BUFFER_SIZE 0

#define ZoO_SERVER_SOCKET_ACCEPT_TIMEOUT_SEC 60
#define ZoO_SERVER_SOCKET_LISTEN_BACKLOG     5

enum ZoO_server_thread_state
{
   ZoO_SERVER_JOINING_THREAD,
   ZoO_SERVER_RUNNING_THREAD,
   ZoO_SERVER_NO_THREAD
};

struct ZoO_server_thread_data
{
#ifndef ZoO_RUNNING_FRAMA_C
   pthread_t posix_id;
#endif
   enum ZoO_server_thread_state state;
};

struct ZoO_server_thread_collection
{
   struct ZoO_server_thread_data * threads;
   size_t threads_capacity;
#ifndef ZoO_RUNNING_FRAMA_C
   pthread_mutex_t mutex;
   pthread_barrier_t barrier;
#endif
   ZoO_index currently_running;
};

struct ZoO_server_socket
{
   int file_descriptor;
   fd_set as_a_set;
   struct timeval timeout;
};

struct ZoO_server_thread_parameters
{
   struct ZoO_server_thread_collection * thread_collection;
   const struct ZoO_parameters * server_params;
   struct ZoO_knowledge * knowledge;
   ZoO_index thread_id;
   int socket;
};

struct ZoO_server_worker
{
   struct ZoO_server_thread_parameters params;
   char * buffer;
   size_t buffer_capacity;
   size_t buffer_length;
   FILE * socket_as_file;
};

struct ZoO_server
{
   struct ZoO_server_thread_collection workers;
   struct ZoO_server_socket socket;
   struct ZoO_server_thread_parameters thread_params;
};

#endif
