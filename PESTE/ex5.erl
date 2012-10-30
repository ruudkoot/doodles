-module(ex5).
-export([main/2]).

main(X,Y) ->
    f1(X),
    g1(Y).
    
f1(1) -> a.
g1(4) -> d.
