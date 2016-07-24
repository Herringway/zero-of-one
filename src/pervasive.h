#ifndef _ZoO_PERVASIVE_H_
#define _ZoO_PERVASIVE_H_

#include <limits.h>

#ifndef ZoO_NETWORK_TIMEOUT
   #define ZoO_NETWORK_TIMEOUT            200
#endif

#ifndef ZoO_MAX_REPLY_WORDS
   #define ZoO_MAX_REPLY_WORDS            64
#endif

#ifndef ZoO_DEFAULT_DATA_FILENAME
   #define ZoO_DEFAULT_DATA_FILENAME      "./memory.txt"
#endif

#ifndef ZoO_DEFAULT_IRC_SERVER_ADDR
   #define ZoO_DEFAULT_IRC_SERVER_ADDR    "irc.foonetic.net"
#endif

#ifndef ZoO_DEFAULT_IRC_SERVER_PORT
   #define ZoO_DEFAULT_IRC_SERVER_PORT    "6667"
#endif

#ifndef ZoO_DEFAULT_IRC_SERVER_CHANNEL
   #define ZoO_DEFAULT_IRC_SERVER_CHANNEL "#theborghivemind"
#endif

#ifndef ZoO_DEFAULT_IRC_USERNAME
   #define ZoO_DEFAULT_IRC_USERNAME       "zeroofone"
#endif

#ifndef ZoO_DEFAULT_IRC_REALNAME
   #define ZoO_DEFAULT_IRC_REALNAME       "Zero of One (bot)"
#endif

#ifndef ZoO_DEFAULT_REPLY_RATE
   #define ZoO_DEFAULT_REPLY_RATE         8
#endif

#ifndef ZoO_MARKOV_ORDER
   #define ZoO_MARKOV_ORDER               2
#endif

typedef unsigned int ZoO_index;
#define ZoO_INDEX_MAX UINT_MAX

/* ZoO_char = UTF-8 char */
typedef char ZoO_char;
/* Functions that can handle UTF-8 'char' will use this symbol. */
#define ZoO_CHAR_STRING_SYMBOL "%s"

#define ZoO__TO_STRING(x) #x
#define ZoO_TO_STRING(x) ZoO__TO_STRING(x)
#define ZoO_ISOLATE(a) do {a} while (0)

/* strncmp stops at '\0' and strlen does not count '\0'. */
#define ZoO_IS_PREFIX(a, b) (strncmp(a, b, strlen(a)) == 0)

#define ZoO_STRING_EQUALS(a, b) (strcmp(a, b) == 0)

#endif
