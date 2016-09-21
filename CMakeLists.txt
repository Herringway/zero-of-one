cmake_minimum_required(VERSION 2.8 FATAL_ERROR)

project("Zero of One")

include(FindPkgConfig)

add_subdirectory(src)
add_definitions(-D_POSIX_SOURCE)
add_definitions(-D_POSIX_C_SOURCE=200809L)

if(CMAKE_COMPILER_IS_GNUCC)
   message(STATUS "GNUCC detected. Adding '-02' parameter.")
   #	set(CMAKE_C_FLAGS "-O2")
   	set(CMAKE_C_FLAGS "-O3")
endif()

# ${SRC_FILES} is recursively defined in the subdirectories.
# Each subdirectory only adds the source files that are present at its level.
add_executable(zero_of_one ${SRC_FILES})
set_property(TARGET zero_of_one PROPERTY C_STANDARD 99)
set_property(TARGET zero_of_one PROPERTY C_STANDARD_REQUIRED ON)
#find_package(Threads)
#target_link_libraries(cborg ${CMAKE_THREAD_LIBS_INIT})
