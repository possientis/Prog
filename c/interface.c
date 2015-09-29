#include <iostream>
#include <string>

using namespace std;

template <typename T>
class INode{

  public:
    virtual INode *next(int x){cout << "base next is not hidden\n"; return nullptr;}
    virtual INode *next() {cout << "This is the base call\n"; return nullptr;}
    virtual T value() = 0;

};


template <typename T>
class Node : public INode<T>{

  T value_; // hasA rather than holdsA
  Node *next_;


  public:
  virtual T value();
  virtual Node *next();
  // Ctor, Dtor
  // Copy constructor for T is being called
  Node(T value): value_(value), next_(nullptr){}
  ~Node(){};
};


template <typename T>
T Node<T>::value() { return value_; }

template <typename T>
Node<T> * Node<T>::next() { return nullptr; }

int main(){

  Node<int> n(23);
  Node<string> m("abc");

  INode<int> *ptr = new Node<int>(46);

  cout << n.value() << endl;
  cout << m.value() << endl;
  cout << (n.next() == nullptr) << endl;

  cout << (ptr->next() == nullptr) << endl;

  delete ptr;

}

