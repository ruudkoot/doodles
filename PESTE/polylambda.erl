-module(polylambda).
-export([main/1]).

main(X) ->
    Id = fun(Y) -> Y end,
    A = Id(0),
    B = Id(1),
    case A of
        1 -> 2
    end.
