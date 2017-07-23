#include <iostream>

template <typename T>
T f(T a);   // declaration


template <> 
int f(int a) { return 2 * a; }

template <>
double f(double a) { return 2.0 * a; }


int main() {

    std::cout << f<int>(1)      << std::endl;
    std::cout << f<double>(2.0) << std::endl;

    return 0;
}
