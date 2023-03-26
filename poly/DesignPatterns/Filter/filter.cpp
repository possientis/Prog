// Filter design pattern
#include <iostream>
#include <string>
#include <vector>
#include <boost/algorithm/string/predicate.hpp> // boost::iequals
#include <functional>

// This pattern allows to use a list of objects and perform
// a filtering operation on that list so as to obtain a new
// list comprised of those objects in the initial list which
// satisfy a given predicate. Since the introduction of
// lambda expressions within Java 8 and the introduction
// of functional interfaces such as Predicate<T>, this 
// pattern is not very useful in practice and amounts 
// mainly to a coding exercise aiming at re-implementing
// the Predicate<T> java interface. This pattern is not
// useful either in functional languages which directly 
// support first class functions and filter operations on lists.

typedef std::string string; // just to make the code nicer

template <typename T> class Predicate {
  public:
    // Constructor
    Predicate(std::function<bool(T)> test):test(test){}
    // Getter method for encapsulated functor 'test'
    bool operator()(T t) const { return test(t);}
    // operations on predicates
    Predicate<T> operator&&(const Predicate<T> other) const;
    Predicate<T> operator||(const Predicate<T> other) const;
    Predicate<T> operator!() const;
    // returns predicate testing == with given targetRef
    static Predicate<T> isEqual(T targetRef);
  private:
    const std::function<bool(T)> test;
};

template<typename T>
Predicate<T> Predicate<T>::operator&&(const Predicate<T> other) const{
  // cannpt capture 'this' in lambda expression used to define 'this'
  // Hence creating variable equal to this->test and capturing that instead
  std::function<bool(T)> pred = test;
  return Predicate<T>([other,pred](T t){ return !pred(t) ? false : other(t); });
}

template<typename T>
Predicate<T> Predicate<T>::operator||(const Predicate<T> other) const{
  // cannpt capture 'this' in lambda expression used to define 'this'
  // Hence creating variable equal to this->test and capturing that instead
  std::function<bool(T)> pred = test;
  return Predicate<T>([other,pred](T t){ return pred(t) ? true : other(t); });
}

template<typename T>
Predicate<T> Predicate<T>::operator!() const{
  // you cannot capture 'this' in lambda expression which is used to define 'this'
  // Hence creating variable equal to this->test and capturing that instead
  std::function<bool(T)>  pred  = test; 
  return Predicate<T>([pred](T t){ return !pred(t); });
}

template<typename T>
Predicate<T> Predicate<T>::isEqual(T targetRef){
  return Predicate<T>([targetRef](T t){ return t == targetRef; });
}

class Person; // forward
class PersonData {
  friend Person;
  private:
    // constructor
    PersonData(string name, string gender, string maritalStatus):
      name(name), 
      gender(gender), 
      maritalStatus(maritalStatus),
      count(1){}
    // destructor
    ~PersonData(){}
    // internal data
    mutable int count;              // reference count
    const string name;
    const string gender;
    const string maritalStatus;
};

typedef std::vector<Person> List; // just to make the code nicer
class Person {
  private:
    const PersonData* data;
    void swap(Person& other){std::swap(data,other.data);} // operator=
  public:
    // constructor
    Person(string name, string gender, string maritalStatus):
      data(new PersonData(name, gender, maritalStatus)){}
    // copy constructor
    Person(const Person &other):data(other.data){ data->count++; }
    // destructor
    ~Person(){ data->count--; if(data->count == 0) delete data; }
    // assignment operator
    Person& operator=(Person rhs){ swap(rhs); return *this; }
    // accessors
    string getName()          { return data->name; }
    string getGender()        { return data->gender; }
    string getMaritalStatus() { return data->maritalStatus; } 

    static List people();                         // see below
    static List filter(List, Predicate<Person>);  // see below
    const static Predicate<Person> male;          // see below
    const static Predicate<Person> female;        // see below
    const static Predicate<Person> single;        // see below
    const static Predicate<Person> singleMale;    // see below
    const static Predicate<Person> singleOrFemale;// see below
};

// plausible implementation of equality for Person objects
bool operator==(Person left, Person right){
  return boost::iequals(left.getName(),right.getName());
}

const Predicate<Person> Person::male = Predicate<Person>([](Person t){
    return boost::iequals(t.getGender(),"MALE");
});

const Predicate<Person> Person::female = Predicate<Person>([](Person t){
    return boost::iequals(t.getGender(),"FEMALE");
});

const Predicate<Person> Person::single = Predicate<Person>([](Person t){
    return boost::iequals(t.getMaritalStatus(),"SINGLE");
});

const Predicate<Person> Person::singleMale = Person::single && Person::male;

const Predicate<Person> Person::singleOrFemale = Person::single || Person::female;

// cout << person
std::ostream& operator<<(std::ostream &s, Person person){
  s << "(" << person.getName() << "," << person.getGender()
    << "," << person.getMaritalStatus() << ")\t";
  return s;
}

std::ostream& operator<<(std::ostream &s, std::vector<Person> list){
  for(Person& person : list){
    std::cout << person;
  }
  return s;
}

List Person::people(){
  std::vector<Person> people;
  people.push_back(Person("Robert","Male","Single"));
  people.push_back(Person("John","Male","Married"));
  people.push_back(Person("Laura","Female","Married"));
  people.push_back(Person("Diana","Female","Single"));
  people.push_back(Person("Mike","Male","Single"));
  people.push_back(Person("Bobby","Male","Single"));
  return people;
}

List Person::filter(List list, Predicate<Person> predicate){
  List newList;
  for(Person& person : list){
    if(predicate(person)) newList.push_back(person);
  }
  return newList;
}

int main(int argc, char* argv[], char* envp[]){

  Person john2("John","Male","Married");
  Predicate<Person> notJohn = !(Predicate<Person>::isEqual(john2));

  auto people           = Person::people();
  auto males            = Person::filter(people, Person::male);
  auto females          = Person::filter(people, Person::female);
  auto singleMales      = Person::filter(people, Person::singleMale);
  auto singleOrFemales  = Person::filter(people, Person::singleOrFemale);
  auto notJohns         = Person::filter(people, notJohn);

  std::cout << "Everyone:\t\t"          << people;
  std::cout << "\nNot John:\t\t"        << notJohns;
  std::cout << "\nSingle or Female:\t"  << singleOrFemales;
  std::cout << "\nMales:\t\t\t"         << males;
  std::cout << "\nSingle Males:\t\t"    << singleMales;
  std::cout << "\nFemales:\t\t"         << females << std::endl;

  return 0;
}


