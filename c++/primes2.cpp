#include <iostream>
#include <sstream>
#include <functional>
#include <string>
#include <assert.h>
// this implementation is utterly useless in terms of performance 

// We assume T is a value type
template <typename T> class Cell;   // forward 

// typedef for generic type
template <typename T> using thunk = std::function<Cell<T>()>;
template <typename T> using predicate = std::function<bool(T)>;
template <typename T> using transition = std::function<T(T)>;
template <typename T> using paramPredicate = std::function<bool(T,T)>;

// We assume T has value type semantics
// We hope that STL type thunk<T> has value type semantics
// Hence we creating a simple type made of two value type fields
template <typename T> class Cell {
  private:
    bool is_null;
     T   car;
    thunk<T>  cdr;

    Cell() : car(0), is_null(true) {}

    Cell(T first, Cell<T> rest) : car(first), is_null(false){
      this->cdr = [rest]() -> Cell<T> { return rest; } ;  // lambda 
    }


//    Cell(const Cell<T>&);               // TBI
//    Cell<T> operator=(const Cell<T>&);  // TBI 

  public:

    bool isNull()   const { return is_null; }
    T first()       const { return car;}
    Cell<T> rest()  const { return cdr(); } // executing thunk

   static Cell<T> null(){
      Cell<T> cell;
      return cell;
    }

   Cell<T> filter(predicate<T> p) const {
      Cell<T> next(*this);
      while(!p(next.first())){
        next = next.rest();
      }

      Cell<T> cell(next.first(), null());
      cell.cdr = [next, p]() -> Cell<T> { return next.rest().filter(p); };
      return cell;
    }

    Cell<T> take(int N){
      assert(N > 0);
      Cell<T> cell(first(), null());
      if(N == 1) return cell;
      Cell<T> that = *this;
      cell.cdr = [that, N]() -> Cell<T> { return that.rest().take(N-1); };
      return cell;
    }

    std::string to_string(){
      std::stringstream str;
      str << "(";

      Cell<T> next = *this;
      bool start = true;
      while(!next.isNull()){
        if(!start) str << " ";
        str << next.first();  // needs to be implemented for T
        start = false;
        next = next.rest();
      }
      str << std::string(")");
      return str.str();
    }


    static Cell<T> fromTransition(T init, transition<T> f){
      Cell<T> cell(init, null());
      cell.cdr = [init,f]() -> Cell<T> { return fromTransition(f(init), f); };
      return cell;
    }

    static Cell<T> sieve(Cell<T> input, paramPredicate<T> p){
      T x = input.first();
      Cell<T> cell(x,null());
      cell.cdr = [input, p, x]()-> Cell<T> { 
        return sieve(input.rest().filter([p,x](T n)->bool{ return p(n,x); }),p);
      };
      return cell;
    }
};

template<typename T>
std::ostream& operator<<(std::ostream& s, Cell<T> list){
  s << list.to_string();
  return s;
}


int main(int argc, char* argv[]){

  if(argc != 2){
    std::cerr << "This program requires a single integer argument\n";
    return EXIT_FAILURE;
  }

  int numPrimes = std::stoi(argv[1]);
  Cell<int> from2 = Cell<int>::fromTransition(2, [](int n)->int{ return n+1; });
  Cell<int> primes = Cell<int>::sieve(
      from2,
      [](int n, int x)-> bool { return n % x != 0; }
  );
  std::cout << primes.take(numPrimes) << std::endl;

  return EXIT_SUCCESS;
}

