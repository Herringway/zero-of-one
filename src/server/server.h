#ifndef _ZoO_SERVER_SERVER_H_
#define _ZoO_SERVER_SERVER_H_

#include "../parameters/parameters_types.h"

#include "server_types.h"

int ZoO_server_initialize
(
   struct ZoO_server server [const restrict static 1],
   const struct ZoO_parameters params [const restrict static 1]
);

int ZoO_server_socket_open
(
   struct ZoO_server_socket server_socket [const restrict static 1],
   const char socket_name [const restrict static 1]
);

void ZoO_server_request_termination (void);
int ZoO_server_is_running (void);
int ZoO_server_set_signal_handlers (void);

int ZoO_server_main
(
   const struct ZoO_parameters params [const restrict static 1]
);

void ZoO_server_finalize (struct ZoO_server [const restrict static 1]);

int ZoO_server_wait_for_new_event
(
   struct ZoO_server server [const restrict static 1]
);

void ZoO_server_handle_joining_threads
(
   struct ZoO_server server [const restrict static 1]
);

int ZoO_server_handle_new_connection
(
   struct ZoO_server server [const restrict static 1]
);

void * ZoO_server_worker_main (void * input);

int ZoO_server_worker_receive
(
   struct ZoO_server_worker worker [const restrict static 1]
);

int ZoO_server_worker_handle_request
(
   struct ZoO_server_worker worker [const restrict static 1]
);

#endif
