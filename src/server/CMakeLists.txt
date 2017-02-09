set(
   SRC_FILES ${SRC_FILES}
   ${CMAKE_CURRENT_SOURCE_DIR}/server.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_create_socket.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_finalize.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_initialize.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_joining_threads.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_new_connection.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_signal.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_wait_for_event.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_worker.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_worker_handle_request.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_worker_receive.c
   ${CMAKE_CURRENT_SOURCE_DIR}/server_worker_send.c
)

set(SRC_FILES ${SRC_FILES} PARENT_SCOPE)

