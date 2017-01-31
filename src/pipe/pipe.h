#ifndef _ZoO_PIPE_PIPE_H_
#define _ZoO_PIPE_PIPE_H_

#include <stdio.h>

#include "../pervasive.h"

#include "pipe_types.h"

#ifndef ZoO_DEBUG_PROGRAM_FLOW
   #define ZoO_DEBUG_PROGRAM_FLOW   (0 || ZoO_DEBUG_ALL)
#endif

#ifndef ZoO_DEBUG_CONFIG
   #define ZoO_DEBUG_CONFIG         (0 || ZoO_DEBUG_ALL)
#endif

#ifndef ZoO_DEBUG_LEARNING
   #define ZoO_DEBUG_LEARNING       (0 || ZoO_DEBUG_ALL)
#endif

#ifndef ZoO_DEBUG_NETWORK
   #define ZoO_DEBUG_NETWORK  1
#endif

#ifndef ZoO_DEBUG_NETWORK
   #define ZoO_DEBUG_NETWORK        (0 || ZoO_DEBUG_ALL)
#endif

#define ZoO_ENABLE_WARNINGS_OUTPUT              1
#define ZoO_ENABLE_RUNTIME_ERRORS_OUTPUT        1
#define ZoO_ENABLE_PROGRAMMING_ERRORS_OUTPUT    1
#define ZoO_ENABLE_FATAL_ERROR_OUTPUT           1

#ifdef ZoO_ENABLE_ERROR_LOCATION
   #define ZoO_LOCATION "[" __FILE__ "][" ZoO_TO_STRING(__LINE__) "]"
#else
   #define ZoO_LOCATION ""
#endif

#define ZoO_PRINT_STDERR(pipe, symbol, str, ...)\
   fprintf(pipe->out, "E [" symbol "]" ZoO_LOCATION " " str "\n", __VA_ARGS__);

/*
 * Given that we use preprocessor contants as flags, we can expect the compilers
 * to remove the test condition for disabled flags. No need to be shy about
 * allowing many debug options.
 */

#define ZoO_DEBUG(pipe, flag, str, ...)\
   ZoO_ISOLATE\
   (\
      if (flag)\
      {\
         ZoO_PRINT_STDERR(pipe, "D", str, __VA_ARGS__);\
      }\
   )


#define ZoO_WARNING(pipe, str, ...)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_WARNINGS_OUTPUT)\
      {\
         ZoO_PRINT_STDERR(pipe, "W", str, __VA_ARGS__);\
      }\
   )

#define ZoO_ERROR(pipe, str, ...)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_RUNTIME_ERRORS_OUTPUT)\
      {\
         ZoO_PRINT_STDERR(pipe, "E", str, __VA_ARGS__);\
      }\
   )

#define ZoO_PROG_ERROR(pipe, str, ...)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_PROGRAMMING_ERRORS_OUTPUT)\
      {\
         ZoO_PRINT_STDERR(pipe, "P", str, __VA_ARGS__);\
      }\
   )

#define ZoO_FATAL(pipe, str, ...)\
   ZoO_ISOLATE\
   (\
     if (ZoO_ENABLE_FATAL_ERROR_OUTPUT)\
      {\
         ZoO_PRINT_STDERR(pipe, "F", str, __VA_ARGS__);\
      }\
   )

/* For outputs without dynamic content (static). ******************************/

#define ZoO_PRINT_S_STDERR(pipe, symbol, str)\
   fprintf(pipe->out, "E [" symbol "]" ZoO_LOCATION " " str "\n");

#define ZoO_S_DEBUG(pipe, flag, str)\
   ZoO_ISOLATE\
   (\
      if (flag)\
      {\
         ZoO_PRINT_S_STDERR(pipe, "D", str);\
      }\
   )

#define ZoO_S_WARNING(pipe, str)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_WARNINGS_OUTPUT)\
      {\
         ZoO_PRINT_S_STDERR(pipe, "W", str);\
      }\
   )

#define ZoO_S_ERROR(pipe, str)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_RUNTIME_ERRORS_OUTPUT)\
      {\
         ZoO_PRINT_S_STDERR(pipe, "E", str);\
      }\
   )

#define ZoO_S_PROG_ERROR(pipe, str)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_PROGRAMMING_ERRORS_OUTPUT)\
      {\
         ZoO_PRINT_S_STDERR(pipe, "P", str);\
      }\
   )

#define ZoO_S_FATAL(pipe, str)\
   ZoO_ISOLATE\
   (\
     if (ZoO_ENABLE_FATAL_ERROR_OUTPUT)\
      {\
         ZoO_PRINT_S_STDERR(pipe, "F", str);\
      }\
   )
#endif
