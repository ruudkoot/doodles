def f():
 x = 0
 def g():
  nonlocal x
  x = x + 1
  return x
 def h():
  nonlocal x
  x = x + 1
  return x
 return [g, h]


