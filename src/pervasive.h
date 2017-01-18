#ifndef _ZoO_PERVASIVE_H_
#define _ZoO_PERVASIVE_H_

#include <limits.h>

#define ZoO_DEBUG_ALL 1

#ifndef ZoO_DEBUG_ALL
   #define ZoO_DEBUG_ALL 0
#endif

#ifndef ZoO_NETWORK_TIMEOUT
   #define ZoO_NETWORK_TIMEOUT            200
#endif

#ifndef ZoO_MAX_REPLY_WORDS
   #define ZoO_MAX_REPLY_WORDS            64
#endif

#define ZoO__TO_STRING(x) #x
#define ZoO_TO_STRING(x) ZoO__TO_STRING(x)
#define ZoO_ISOLATE(a) do {a} while (0)

/* strncmp stops at '\0' and strlen does not count '\0'. */
#define ZoO_IS_PREFIX(a, b) (strncmp(a, b, strlen(a)) == 0)

#define ZoO_STRING_EQUALS(a, b) (strcmp(a, b) == 0)

#endif
