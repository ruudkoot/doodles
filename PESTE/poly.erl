-module(poly).
-export([main/1]).

main(X) ->
    A = id(0),
    B = id(1),
    case A of
        1 -> 2
    end.

id(X) ->
    X.
