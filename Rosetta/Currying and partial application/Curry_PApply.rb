def f
  proc {|a, b, x| a * x + b}
end

def f2(a, b, x)
  a * x + b
end

def g
  proc {|a| proc {|b| proc {|x| a * x + b}}}
end

def main
  u = f.curry
  v = f.curry[7,9]
  w = g[7][9]
  puts [ (1..5).map {|x| u[7][9][x]} \
       , (1..5).map {|x| v[x]}       \
       , (1..5).map {|x| w[x]}       ]
end

main

