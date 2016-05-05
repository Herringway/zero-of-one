cmake_minimum_required(VERSION 2.8 FATAL_ERROR)

project("Zero of One")

include(FindPkgConfig)

add_subdirectory(src)
set(CMAKE_C_FLAGS "-D_POSIX_SOURCE -std=c99 -O2")
# ${SRC_FILES} is recursively defined in the subdirectories.
# Each subdirectory only adds the source files that are present at its level.
add_executable(zero_of_one ${SRC_FILES})
