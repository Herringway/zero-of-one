# zero-of-one
(Yet another) Markov chain based reply bot.

## Dependencies
- D compiler.
- Dub.

## Quick setup guide (IRC)
```
$ git clone https://github.com/herringway/zero-of-one.git
$ cd zero-of-one
$ dub run :ircbot
$ $EDITOR settings.yml
$ dub run :ircbot
```

## Quick setup guide (CLI)
```
$ git clone https://github.com/herringway/zero-of-one.git
$ cd zero-of-one
$ dub run :cmdline -- [paths to extra text files here]
```

## Main Objectives
- Paranoia levels of error checking.
- Low RAM usage.
- Giggles.

## Behavior
- Replies when it reads messages containing a word matching its NICKNAME or one
   of its ALIASes. (IRC only)
- Replies to messages with a REPLY_RATE percent chance. The word used to
   construct the reply is the less known one. (IRC only)
- Reacts to user joining in. If the username is in enough samples, it is used
   to construct the greeting, otherwise a random word is selected as starting
   point. (IRC only)
- Repetition is taken into account and augments the strength of the links.
- Some punctuation symbols are identified (e.g. "example." will be understood
   as "example" followed by ".").
