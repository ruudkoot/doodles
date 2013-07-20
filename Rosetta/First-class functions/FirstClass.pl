sub f {
    my $a = 3;
    my $b = 1;
    return ( sub { my @xs = $_[0]; map { $a * $_ + $b } @xs }
           , sub { my @xs = $_[0]; map { $b * $_ + $a } @xs } );
}

@xs = (1,2,3,4,5);
($f,$g) = f();
print ($f->(@xs), $g->(10));
# print $g->(7);

sub g {
    return map {$_+1} $_[0];
}

print "\n", g(@xs)
