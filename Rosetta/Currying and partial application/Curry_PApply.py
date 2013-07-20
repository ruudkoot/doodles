from functools import partial

def curry3(f):
  return lambda a: lambda b: lambda x: f(a, b, x)

def f(a, b, x):
  return a * x + b

def g(a):
  return lambda b: lambda x: a * x + b

def main():
  u = curry3(f)(7)(9)
  v = partial(f, 7, 9)
  w = g(7)(9)
  print [map(u, [1,2,3,4,5]), map(v, [1,2,3,4,5]), map(w, [1,2,3,4,5])]
  
main()
