module pervasive;

enum ZoO_NETWORK_TIMEOUT = 200;

enum ZoO_MAX_REPLY_WORDS =  64;

enum ZoO_DEFAULT_DATA_FILENAME = "./memory.txt";

enum ZoO_DEFAULT_IRC_SERVER_ADDR = "anarchy.esper.net";

enum ZoO_DEFAULT_IRC_SERVER_PORT = "6667";

enum ZoO_DEFAULT_IRC_SERVER_CHANNEL = "#hway-test";

enum ZoO_DEFAULT_IRC_USERNAME = "zeroofone";

enum ZoO_DEFAULT_IRC_REALNAME = "Zero of One (bot)";

enum ZoO_DEFAULT_REPLY_RATE = 8;

enum ZoO_MARKOV_ORDER = 3;

alias ZoO_index = uint;
enum ZoO_INDEX_MAX = uint.max;

/* ZoO_char = UTF-8 char */
alias ZoO_char = char;
/* Functions that can handle UTF-8 'char' will use this symbol. */
enum ZoO_CHAR_STRING_SYMBOL = "%s";

//#define ZoO__TO_STRING(x) #x
//#define ZoO_TO_STRING(x) ZoO__TO_STRING(x)
//#define ZoO_ISOLATE(a) do {a} while (0)

/* strncmp stops at '\0' and strlen does not count '\0'. */
//#define ZoO_IS_PREFIX(a, b) (strncmp(a, b, strlen(a)) == 0)

//#define ZoO_STRING_EQUALS(a, b) (strcmp(a, b) == 0)
