-module(ex1).
-export([main/1]).

main(A) ->
    X = f(A),
    case X of
        0 -> g(X);
        _ -> g(X-1)
    end.
    
    f(X) -> X+1.
    
    g(42) -> ok.
