program Adhoc;

function Outer( x : Integer ) : Integer;
        function Inner( y : Integer ) : Integer;
        begin
                Inner := x + y;
        end;
begin
        Writeln('Haha');
        Outer := 42; //Inner(42);
end;

begin
        Writeln(Outer(7));
end.
