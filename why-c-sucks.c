#include <stdio.h>

int main(int argc, char** argv) {
    int x, y;
    y = f() * g();
    x = y + y;
    // x = f() * g() + f() * g();
}

int f() {
    printf("F");
    return fib(25);
}

int g() {
    printf("G");
    return fib(30);
}

int fib(int n) {
    switch (n) {
        case 0:
            return 0;
        case 1:
            return 1;
        default:
            return fib(n-1) + fib(n-1);            
    }
}
