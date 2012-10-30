-module(map).
-export([main/1]).
-export([map/2]).

main(X) ->
    A = id(0),
    B = id(1),
    case A of
        1 -> 2
    end.

id(X) -> X.

map(F,L) ->
    case L of
        [] -> [];
        [X|XS] -> [F(X)|map(F,XS)]
    end.
