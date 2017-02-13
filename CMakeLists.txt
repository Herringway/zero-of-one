cmake_minimum_required(VERSION 3.0 FATAL_ERROR)

project("Zero of One - server")

include(FindPkgConfig)

add_subdirectory(src)
add_definitions(-D_POSIX_SOURCE)
add_definitions(-D_POSIX_C_SOURCE=200809L)

if(CMAKE_COMPILER_IS_GNUCC)
   #   message(STATUS "GNUCC detected. Adding '-03' parameter.")
   #	set(CMAKE_C_FLAGS "-O2")
   	set(CMAKE_C_FLAGS " -g")
endif()

# ${SRC_FILES} is recursively defined in the subdirectories.
# Each subdirectory only adds the source files that are present at its level.
add_executable(ZoO_server ${SRC_FILES})
set_property(TARGET ZoO_server PROPERTY C_STANDARD 99)
set_property(TARGET ZoO_server PROPERTY C_STANDARD_REQUIRED ON)
find_package(Threads)
target_link_libraries(ZoO_server ${CMAKE_THREAD_LIBS_INIT})

## OPTION HANDLING #############################################################
# TODO
