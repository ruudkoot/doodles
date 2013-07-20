program Adhoc;

function Add( x, y : Integer ) : Integer;
begin
        Add := x + y
end;

function Add( s, t : String ) : String;
begin
        Add := Concat( s, t )
end;

begin
        Writeln(Add(1, 2));
        Writeln(Add('Hello, ', 'World!'));
end.