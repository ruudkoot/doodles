-module(poly2).
-export([main/1]).

main(X) ->
    A = zero(X),
    B = one(X),
    case X of
        2 -> 0
    end.
    
nd(X) ->
    case X of
        0 -> 0;
        1 -> 1
    end.
    
zero(X) ->
    case X of
        0 -> 0
    end.
    
one(X) ->
    case X of
        1 -> 1
    end.

id(X) ->
    X.
