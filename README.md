# zero-of-one-prototype
(Yet another) Markov chain based IRC reply bot.
### Deprecated:
This is the prototype that led to the Zero of One bot, it is known to
have stability issues. Users are encouraged to switch to the actual
Zero of One bot (which uses a Server/Filters/Gateways architecture) as
soon as possible. As all learned data is stored in plain text, switching
should not cause any issues.

## Dependencies
- POSIX compliant OS.
- D compiler.
- Dub.

## Quick setup guide
```
$ git clone https://github.com/herringway/zero-of-one.git
$ cd zero-of-one
$ dub build
$ ./zero_of_one -h
Usage: ./zero_of_one [option_1 option_2 ...] NICKNAME [ALIAS_1 ALIAS_2 ...]
NICKNAME is used as the IRC nickname value.
If NICKNAME or any ALIAS is found in an event, the program will reply.

Available options:
   [--data-filename | -df] FILENAME
      Learn content from FILENAME before connecting.
      Default: ./memory.txt.
   [--new-data-filename | -ndf] FILENAME
      Store new data learned in FILENAME.
      Default: value of the --data-filename param.
   [--irc-server-addr | -isa] IRC_SERVER_ADDR
      Connect to this server address.
      Default: irc.foonetic.net.
   [--irc-server-port | -isp] IRC_SERVER_PORT
      Connect to this server port.
      Default: 6667.
   [--irc-server-channel | -isc] IRC_SERVER_CHANNEL
      Connect to this server's channel.
      Default: #theborghivemind.
   [--irc-username | -iu] USERNAME
      Connect using this as 'username' (shown in WHOIS).
      Default: zeroofone.
   [--irc-realname | -ir] REALNAME
      Connect using this as 'realname' (shown in WHOIS).
      Default: Zero of One (bot).
   [--reply-rate | -rr] REPLY_RATE
      Chance to reply to an event (integer, range [0, 100]).
      Default: 8.
```
Note that if the NICKNAME has a uppercase character, it will never be matched by
any inputs, as all inputs are converted to lowercase. A simple solution is to
have a lowercase version of NICKNAME in the ALIAS list.

## Main Objectives
- POSIX compliance.
- Paranoia levels of error checking.
- Low RAM usage.
- Giggles.

## Behavior
- Replies when it reads messages containing a word matching its NICKNAME or one
   of its ALIASes.
- Replies to messages with a REPLY_RATE percent chance. The word used to
   construct the reply is the less known one.
- Reacts to user joining in. If the username is in enough samples, it is used
   to construct the greeting, otherwise a random word is selected as starting
   point.
- Repetition is taken into account and augments the strength of the links.
- Some punctuation symbols are identified (e.g. "example." will be understood
   as "example" followed by ".").
