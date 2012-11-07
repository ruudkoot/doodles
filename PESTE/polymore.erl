-module(polymode).
-export([f/1,g/1]).

f(X) ->
    A = id(0),
    % B = id(1),
    case A of
        1 -> 2
    end.

g(X) ->
    A = id(0),
    case A of
        1 -> 2
    end.

id(X) -> X.
