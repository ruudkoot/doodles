-module(useless).
-compile([debug_info, export_all]).
-export([add/2, hello/0, greet_and_add_two/1]).
-import(io, [format/1]).
-define(sub(X,Y), X-Y).

add(A,B) ->
    A + B.

%% Shows greetings.
hello() ->
    format("Hello, world!~n").
    
greet_and_add_two(X) ->
    hello(),
    _ = ?sub(23,47),
    add(X,2).
