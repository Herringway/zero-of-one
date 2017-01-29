add_subdirectory(cli)
add_subdirectory(core)
add_subdirectory(knowledge)
add_subdirectory(pipe)
add_subdirectory(server)
add_subdirectory(sequence)
add_subdirectory(storage)

set(
   SRC_FILES ${SRC_FILES}
   ${CMAKE_CURRENT_SOURCE_DIR}/main.c
)

set(SRC_FILES ${SRC_FILES} PARENT_SCOPE)
