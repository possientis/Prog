


int main(){

  auto f = [](double x) -> double { return x*x - 0.5;};
  auto g = [](double x){ return x*x - 0.5; };

  typedef decltype(f) function_f; // function_f is the type of f

  return 0;
}
