#include <iostream>
#include <string>

using namespace std;

void test();

int main(int argc, char* arg[]) {
    cout << "Hello, world!" << endl;
    test();
    return 0;
}

void test() {

    auto f = [&] { string s = "TEST 1 2 3";
                   return s;
                 };
                 
    cout << f() << endl;
}

