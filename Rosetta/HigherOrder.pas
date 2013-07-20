function PlusFive( x : Integer ) : Integer;
begin
        PlusFive := x + 5;
end;

function Apply( function f( Integer ) : Integer, x : Integer ) : Integer;
begin
        Apply := f(x);
end;

begin
        Writeln( Apply( PlusFive, 42 ) );
end.
