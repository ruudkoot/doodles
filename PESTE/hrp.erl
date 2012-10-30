-module(hrp).
-export([main/1]).

main(X) ->
    A = id(id(0)),
    B = id(id(1)),
    case A of
        1 -> 0
    end.

id(X) ->
    X.
