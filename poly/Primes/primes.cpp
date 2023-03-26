// The performance of this code is disappointing. When writing lambda
// expression literals which capture an std::function, passing such
// captured function by reference makes a substantial difference in the 
// code performance (e.g. 25% speed up for 2000 primes).
// Unfortunately, this may destroy correctness.


// We did not implement memoization in the thunk. We initially forgot,
// then realized it had no beneficial impact in the Scheme implementation

#include <iostream>
#include <sstream>
#include <functional>
#include <string>
#include <assert.h>


template <typename T> class Cell;   // forward 

// typedef for generic type
template <typename T> using Thunk = std::function<Cell<T>()>;
template <typename T> using Transition = std::function<T(T)>;
template <typename T> using Predicate = std::function<bool(T)>;
template <typename T> using ParamPredicate = std::function<bool(T,T)>;

template <typename T> class CellImpl {
  friend Cell<T>;
  private:
    CellImpl(T car, Thunk<T> thunk):count(1), car(car), cdr(thunk){}
    int count;  // reference count
    const T  car;
    Thunk<T> cdr;
};

// We assume that T has value semantics:
// 1. operator= is defined
// 2. it has copy constructor
// 
template <typename T> class Cell {
  private:
    static long memory_check;
    CellImpl<T> *_impl;
    Cell(){}
    Cell(T first, Cell<T> rest);      
    void swap(Cell<T> &rhs);          // private no fail swap for operator=
    Cell<T>& operator=(Cell<T> rhs);  // rhs passed by value (code gets copy)
  public:
    ~Cell();
    Cell(const Cell<T> & rhs);
    T first() const { assert(_impl != nullptr); return _impl->car; }
    Cell<T> rest() const { assert(_impl != nullptr); return _impl->cdr(); } 
    bool is_null() const { return _impl == nullptr; }
    Cell<T> take(int N) const;
    std::string to_string();
    Cell<T> filter(const Predicate<T>& p);
    static const Cell<T> null;
    static const Cell<T> null_init();
    static Cell<T> fromTransition(T init, const Transition<T>& f);
    static Cell<T> sieve(Cell<T> input, const ParamPredicate<T>& p);
};

template <typename T>
long Cell<T>::memory_check = 0L;

template <typename T> 
const Cell<T> Cell<T>::null = Cell<T>::null_init();

template <typename T>
const Cell<T> Cell<T>::null_init(){ 
  Cell<T> temp; 
  temp._impl = nullptr; 
  return temp; 
}

template <typename T>
Cell<T>::Cell(T first, Cell<T> rest){
  _impl = new CellImpl<T>(
      first,
      [rest]() -> Cell<T>{ return rest; }   // lambda
  );
  assert(_impl != nullptr);
//  memory_check ^= (long) _impl;
//  std::cerr << "Allocating cell " << std::hex << memory_check << std::endl;
}

template <typename T>
Cell<T>::Cell(const Cell<T> &rhs):_impl(rhs._impl){
  if(_impl != nullptr) _impl->count++;
}

template <typename T>
Cell<T>::~Cell(){
  if(_impl != nullptr){       // nothing to do if null object
    assert(_impl->count > 0); 
    _impl->count--;
    if(_impl->count == 0){
      delete _impl;
//      memory_check ^= (long) _impl;
//     std::cerr << "Deallocating cell " << std::hex << memory_check << std::endl;
      _impl = nullptr;        // safety
    }
  }
}

template <typename T>
void Cell<T>::swap(Cell<T>& rhs){
  std::swap(_impl, rhs._impl); 
}

template <typename T>
Cell<T> & Cell<T>::operator=(Cell<T> rhs){
  swap(rhs);
  return *this;
}


template <typename T>
Cell<T> Cell<T>::fromTransition(T init, const Transition<T> &f){
  Cell<T> cell(init,null);
  cell._impl->cdr = [init,&f]() -> Cell<T> { return fromTransition(f(init),f); };
  return cell;
}

template <typename T>
Cell<T> Cell<T>::take(int N) const {
  assert(N > 0);
  Cell<T> cell(first(), null);
  if(N == 1) return cell;
  Cell<T> that(*this);
  cell._impl->cdr = [that, N]() -> Cell<T> { return that.rest().take(N-1); };
  return cell;
}

template <typename T>
std::string Cell<T>::to_string(){
  std::stringstream str;
  str << "(";
  Cell<T> next = *this;
  bool start = true;
  while(!next.is_null()){  // trouble unless stream is finite
    if(!start) str << " ";
    str << next.first();  // needs to be implemented for T
    start = false;
    next = next.rest();
  }
  str << std::string(")");
  return str.str();
}

template <typename T>
Cell<T> Cell<T>::filter(const Predicate<T>& p){
  Cell<T> next(*this);
  while(!p(next.first())){
    next = next.rest();
  }
  Cell<T> cell(next.first(), null);
  // do not capture predicate p by reference as in '[next, &p]' as this
  // will make the whole program fail, for a reason which is not understood.
  cell._impl->cdr = [next, p]() -> Cell<T> { return next.rest().filter(p); };
  return cell;
}

template <typename T>
Cell<T> Cell<T>::sieve(Cell<T> input, const ParamPredicate<T>& p){
  T x = input.first();
  Cell<T> cell(x, null);
  // passing p by reference here produces 25% saving time on 2000 primes
  // without affecting correctness (for reasons which are not understood)
  cell._impl->cdr = [input, &p, x]() -> Cell<T> {
    return sieve(input.rest().filter([&p,x](T n)->bool{ return p(n,x); }), p);
  };
  return cell;
} 

template <typename T>
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
