#ifndef _ZoO_ERROR_ERROR_H_
#define _ZoO_ERROR_ERROR_H_

#include <stdio.h>

#include "../pervasive.h"

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
   #define ZoO_LOCATION " [" __FILE__ "][" ZoO_TO_STRING(__LINE__) "]"
#else
   #define ZoO_LOCATION ""
#endif

#define ZoO_PRINT_STDERR(io, symbol, str, ...)\
   fprintf(io, "[" symbol "]" ZoO_LOCATION " " str "\n", __VA_ARGS__);

/*
 * Given that we use preprocessor contants as flags, we can expect the compilers
 * to remove the test condition for disabled flags. No need to be shy about
 * allowing many debug options.
 */

#define ZoO_DEBUG(io, flag, str, ...)\
   ZoO_ISOLATE\
   (\
      if (flag)\
      {\
         ZoO_PRINT_STDERR(io, "D", str, __VA_ARGS__);\
      }\
   )


#define ZoO_WARNING(io, str, ...)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_WARNINGS_OUTPUT)\
      {\
         ZoO_PRINT_STDERR(io, "W", str, __VA_ARGS__);\
      }\
   )

#define ZoO_ERROR(io, str, ...)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_RUNTIME_ERRORS_OUTPUT)\
      {\
         ZoO_PRINT_STDERR(io, "E", str, __VA_ARGS__);\
      }\
   )

#define ZoO_PROG_ERROR(io, str, ...)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_PROGRAMMING_ERRORS_OUTPUT)\
      {\
         ZoO_PRINT_STDERR(io, "P", str, __VA_ARGS__);\
      }\
   )

#define ZoO_FATAL(io, str, ...)\
   ZoO_ISOLATE\
   (\
     if (ZoO_ENABLE_FATAL_ERROR_OUTPUT)\
      {\
         ZoO_PRINT_STDERR(io, "F", str, __VA_ARGS__);\
      }\
   )

/* For outputs without dynamic content (static). ******************************/

#define ZoO_PRINT_S_STDERR(io, symbol, str)\
   fprintf(io, "[" symbol "]" ZoO_LOCATION " " str "\n");

#define ZoO_S_DEBUG(io, flag, str)\
   ZoO_ISOLATE\
   (\
      if (flag)\
      {\
         ZoO_PRINT_S_STDERR(io, "D", str);\
      }\
   )

#define ZoO_S_WARNING(io, str)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_WARNINGS_OUTPUT)\
      {\
         ZoO_PRINT_S_STDERR(io, "W", str);\
      }\
   )

#define ZoO_S_ERROR(io, str)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_RUNTIME_ERRORS_OUTPUT)\
      {\
         ZoO_PRINT_S_STDERR(io, "E", str);\
      }\
   )

#define ZoO_S_PROG_ERROR(io, str)\
   ZoO_ISOLATE\
   (\
      if (ZoO_ENABLE_PROGRAMMING_ERRORS_OUTPUT)\
      {\
         ZoO_PRINT_S_STDERR(io, "P", str);\
      }\
   )

#define ZoO_S_FATAL(io, str)\
   ZoO_ISOLATE\
   (\
     if (ZoO_ENABLE_FATAL_ERROR_OUTPUT)\
      {\
         ZoO_PRINT_S_STDERR(io, "F", str);\
      }\
   )
#endif
