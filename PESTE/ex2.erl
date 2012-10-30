-module(ex2).
-export([main/1]).

main(A) ->
    X = f(A),
    Y = g(A,0),
    Z = f(Y),
    case Z of
        0 -> g(X,A);
        _ -> g(X-1,0)
    end.

f(0) -> 0;
f(1) -> 1.

g(1,0) -> 0.
