#include <stdio.h>

int l(int x) {
 return 2 * x + 1;
}

int (*compose(int (*)(int), int (*)(int)))(int);

int (*compose(int (*f)(int), int (*g)(int)))(int) {
 return f;
}

void main(void) {
  int (*r)(int) = compose(l, l);
  int y = r(42);
  printf("%i\n", y);
}


