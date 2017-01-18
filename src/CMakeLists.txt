add_subdirectory(cli)
add_subdirectory(core)
add_subdirectory(file)
add_subdirectory(irc)
add_subdirectory(knowledge)
add_subdirectory(tool)

set(
   SRC_FILES ${SRC_FILES}
   ${CMAKE_CURRENT_SOURCE_DIR}/main.c
)

set(SRC_FILES ${SRC_FILES} PARENT_SCOPE)
