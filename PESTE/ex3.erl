% example 3
-module(ex3).
-export([main/1]).

main(X) ->
    case 3 of
        X ->
            case X of
                2 -> 0
            end;
        _ -> 1
    end.
