def counter():
    x = 0
    def increment(y):
        nonlocal x
        x += y
        print(x)
    def decrement(y):
        nonlocal x
        x -= y
        print(x)
    return [increment, decrement]
 
[counter1_increment, counter1_decrement] = counter()
[counter2_increment, counter2_decrement] = counter()
 
counter1_increment(1)    # prints 1
counter1_increment(7)    # prints 8
counter2_increment(1)    # prints 1
counter1_increment(1)    # prints 9
counter1_decrement(5)    # prints 4
