from functools import partial

def f():
    a = 1
    b = 3
    return [ partial(map, lambda x: a * x + b)
           , partial(map, lambda x: b * x + a) ]
    
print map(lambda g: g([1, 2, 3, 4, 5]), f())

