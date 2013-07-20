def counter():
    x = 0
    def increment():
        nonlocal x
        x += 1
        print(x)
        
    def decrement():
        nonlocal x
        x -= 1
        print(x)
        
    return increment
    
counter1_increment = counter()
counter2_increment = counter()

counter1_increment()
# 1
counter1_increment()
# 2
counter2_increment()
# 1
counter1_increment()
# 3
