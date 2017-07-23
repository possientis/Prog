#include <iostream>

template <typename F,typename G>
auto operator*(G g,F f) {
    return [&](auto x) { return g(f(x)); } ;
}


template <typename T>
T id(T x) {
    return x;
}


int main() {
    auto f = [](int x) -> float { return ((float) x) * 2.0; };
    auto g = [](float y) -> int {return ((int) y) * 3; };

    std::cout << (g * f)(5) << "\n";

    return 0;
}
