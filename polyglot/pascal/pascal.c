#include <iostream>
#include <string>
#include <list>
#include<iterator>
#include <assert.h>

// This is Java code witten in C++
// Interesting to note that it seems a lot faster than corresponding Java
// However the C++ code is littered with explicit 'delete' clean up calls.
// So need to redesign it with smart pointers


// unlike Java List<E> or C# IList<T>, C++ STL does not provide an interface
// on which to rely in order abstract the code away from implementation specifics
// hence we are creating a protocol class for that purpose. Such protocol class
// has a key method returning a concrete object of some iterator class which 
// implements some iterator interface, which we shall need to define too:

// Somehow it looks like we are creating an adaptor (or is it facade?) to give 
// C++ STL some simple Java looking interface, so we can easily translate Java 

// Attempting to create something similar to Java interface Iterator<Integer>
// while avoiding generic programming for the purpose of this exercise, as
// we are only dealing with type 'int'.
class IIterator{
  public:
  virtual ~IIterator(){};
  virtual bool hasNext() const =0;
  virtual int next() =0;
};
  
// Attempting to create something similar to Java interface List<Integer>
class IList{
  public:
  virtual ~IList(){};
  virtual void addFront(int) =0;
  virtual void addBack(int)  =0;
  virtual void addAll(const IList*) =0;
  virtual IIterator* iterator() const =0;
  virtual std::string toString() const =0;
};

class List; // forward declaration needed to declare it friend of Iterator

// some implemenatation of IIterator based on STL
class Iterator : public IIterator {
  Iterator(std::list<int>&);  // private
  friend List;  // iterator method of List will create Iterator
  Iterator(const Iterator&);            // not implemented
  Iterator& operator=(const Iterator&); // not implemented
  std::list<int>::iterator _begin;
  std::list<int>::iterator _end;
  std::list<int>::iterator _current;
  public:
  ~Iterator(){}
  bool hasNext() const override;
  int next() override;
};

// some implementation of IList based on STL containers, which we shall use
// in order to test the code (which only relies on the protocol class IList)
class List : public IList {
  List(const List&);              // not implemented
  List& operator=(const List&);   // not implemented
  std::list<int> *_data;          // some reasonable STL container class
  public:
  List(){_data = new std::list<int>();}
  ~List(){delete _data;}
  std::string toString() const override;
  void addFront(int x) override{_data->push_front(x);}
  void addBack(int x) override{_data->push_back(x);}
  void addAll(const IList* list) override;
  IIterator* iterator() const override;
}; 

// List Iterator implementation
// Attempting to replicate Java semantics
Iterator::Iterator(std::list<int>& list): _begin(list.begin()), _end(list.end()){
   _current = _begin;
}

bool Iterator::hasNext() const{
  return _current != _end;
}

int Iterator::next(){
  return *_current++;
}


// List implementation
IIterator* List::iterator() const{
  assert(_data != nullptr);
  return new Iterator(*_data);  // don't dont forget to clean up
}

void List::addAll(const IList* list){
  IIterator* iter = list->iterator();
  assert(iter != nullptr);
  while(iter->hasNext()){
    addBack(iter->next());
  }
  delete iter;  // don't forget to delete your iterator
}

std::string List::toString() const {
  bool start = true;
  std::string strOut = "";
  IIterator* iter = iterator();
  if(!iter->hasNext()){ // empty list
    strOut += "[]";
  }
  else{
    while(iter->hasNext()){
      if(start){
        strOut += '[';
      }
      else{
        strOut += ',';
      }
      start = false;
      strOut += std::to_string(iter->next());
    }
    strOut += ']';
  }
  delete iter;
  return strOut;
}


// The main work has been done, we can now simply translate Java code.
// while remembering to clean up heap allocations.

// factory method returning some IList based on our implementation choice
IList *newList(){
  return new List();  // remember to clean up
}
   
static IList* shiftLeft(IList* list){
  IList *temp = newList();
  temp->addAll(list);
  assert(temp != nullptr);
  temp->addBack(0);
  return temp;
}

static IList* shiftRight(IList* list){
  IList *temp = newList();
  temp->addAll(list);
  assert(temp != nullptr);
  temp->addFront(0);
  return temp;
}

static IList* addList(IList* list1, IList* list2){
  IList *temp = newList();
  IIterator* iter1 = list1->iterator();
  IIterator* iter2 = list2->iterator();
  while(iter1->hasNext()){
    temp->addBack(iter1->next() + iter2->next());
  }
  delete iter1; // don't forget
  delete iter2; // don't forget

  return temp;
}

static IList *fastPascal(int n){
  if(n == 1){
    IList* list = newList();
    list->addBack(1);             // IList needs an 'add' method
    return list;
  }
  else{
    IList* list = fastPascal(n-1);
    IList* list1 = shiftLeft(list); // need to keep track of object for clean up
    IList* list2 = shiftRight(list); //
    delete list;
    list = addList(list1,list2);
    delete list1;
    delete list2;
    return list;
  }
}

int main(int argc, char* argv[]){
  IList *list = fastPascal(20);
  std::cout << list->toString() << std:: endl;
  delete list;  // we have to do this for lack of better design
  return 0;
}
