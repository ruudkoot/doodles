-module(ho).
%-export([main/1]).
-export([test/1]).
-export([id/1]).
-export([f/1]).

%main(X) ->
%    test(fun f/1).

test(F) ->
    A = f(1),
    case A of
        q -> w
    end.

id(X) -> X.

f(X) ->
    case X of
        1 -> 2;
        Y -> Y+1
    end.
