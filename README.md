[![Build Status](https://travis-ci.org/zyla/coq-webapp.svg?branch=master)](https://travis-ci.org/zyla/coq-webapp)

Web app (frontend only) writen in Coq.
Compiled to JS via BuckleScript. Uses `bucklescript-tea` Elm clone library.

Currently there's only one Coq module (`Main.v`) which contains bindings to TEA,
application code and extraction.

# Development

Dependencies: `yarn`

BuckleScript watcher: `yarn watch`

HTTP server for the app: `yarn server`

Compiling the Coq module will trigger BuckleScript watcher, and in turn
livereload.
