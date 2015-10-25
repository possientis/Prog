#include <iostream>
#include <string>
#include <list>
#include<iterator>
#include <assert.h>


// unlike Java List<E> or C# IList<T>, C++ STL does not provide an interface
// on which to rely in order abstract the code away from implementation specifics
// hence we are creating a protocol class for that purpose
class IList{
  public:
  virtual void addFront(int) =0;
  virtual void addBack(int)  =0;
  virtual std::string toString() const =0;
  virtual ~IList(){};
};

// some implementation of IList based on STL containers, which we shall use
// in order to test the code (which only relies on the protocol class IList)
class List : public IList {
  List(const List&);              // not implemented
  List& operator=(const List&);   // not implemented
  std::list<int> *_data;

  public:
  static int count;               // debug stage: keeps track of ctor/dtor
  List(){++count; _data = new std::list<int>();}
  ~List(){--count; delete _data;}
  std::string toString() const override;
  void addFront(int x) override{_data->push_front(x);}
  void addBack(int x) override{_data->push_back(x);}
}; 


// List implementation

// non-const static member initialization
int List::count = 0;

std::string List::toString() const {
  return std::string("List:") + std::to_string(count);
}


// Actual pascal code

// factory method returning some IList based on our implementation choice
IList *newList(){
  return new List();  // someone needs to clean this up, unsafe
}
   
static IList* shiftLeft(IList* list){
  IList *temp = newList();
  // need to copy list
  assert(temp != nullptr);
  temp->addBack(0);
  return temp;
}


static IList* shiftRight(IList* list){
  IList *temp = newList();
  // need to copy list
  assert(temp != nullptr);
  temp->addFront(0);
  return temp;
}

static IList* addList(IList* list1, IList* list2){
//  IList *temp = newList();

  return newList();
}

static IList *fastPascal(int n){
  if(n == 1){
    IList* list = newList();
    list->addBack(1);             // IList needs an 'add' method
    return list;
  }
  else{
    IList* list = fastPascal(n-1);
    IList* list1 = shiftLeft(list);
    IList* list2 = shiftLeft(list);
    delete list;
    list = addList(list1,list2);
    delete list1;
    delete list2;
    return list;
  }
}

int main(int argc, char* argv[]){

  IList *list = fastPascal(3);
  std::cout << list->toString() << std::endl; // IList needs a 'toString' method

  delete list;  // we have to do this for lack of better design

  return 0;

}
