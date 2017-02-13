# zero-of-one-server
Server for Zero of One, a K-order Markov chain reply bot.

## WARNING
This is an alpha version, both the software and the protocol are subject to
changes. There is currently no stable version.

## Description
This is a multi-threaded K-order Markov chain reply bot. It uses its own
text-based protocol over UNIX sockets as only interface, meaning that it cannot
directly connect to IRC/Discord/Twitch/etc servers. Instead, it relies on
gateway applications to be the actual clients. This allows the same Zero of One
server to talk to any number of gateways (e.g. you can use the same instance of
the bot on both IRC and Discord). Moreover, it can be used while loading input
files, as those are simply considered to be gateways.

Following the UNIX philosophy, it allows for any number of filter programs to be
set up between any number of gateway and the server, as long as they use the
protocol.

This particular implementation of a Zero of One server keeps all its knowledge
in RAM and stores learned inputs into a text file.

Learning multiple times the exact same input is supported, it strengthens the
links between the involved words.

## Dependencies
- POSIX compliant OS.
- C compiler (with C99 support).
- CMake.

## How to use?
The ZoO protocol uses text based exchanges over UNIX sockets. If you were to
use this server for an IRC bot, you'd have to at least get a Zero of One to IRC
gateway, then connect it to the server. You may also want to add filter programs
between the gateway and the server.

### Starting the server.
### Adding filters.
### Adding a gateway.
### Loading data.
The recommended method of loading previously learned data into the server is to
use the Zero of One CLI gateway:
```$ cat my_storage_file | sed -e 's/^/?RL /' | ./ZoO_cli SERVER_SOCKER_NAME
```
To load new data, it would be preferable to go through the filters instead,
and to also request the storing of the newly learned lines:
```$ cat my_new_file | sed -e 's/^/?RLS /' | ./ZoO_cli FILTER_SOCKER_NAME
```
