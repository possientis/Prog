// Filter design pattern
#include <iostream>
#include <string>
#include <vector>
#include <boost/algorithm/string/predicate.hpp> // boost::iequals

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

typedef std::string string;

template <class T> class Predicate {
  public:
    bool operator()(T t) const;
    /*
    static Predicate<T> isEqual(T targetRef){
      return [targetRef](T t){t == targetRef;};
    }
    Predicate<T> operator!(){ // not
      return [this](T t){!this->operator()(t);};
    }
    */
};




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

    static std::vector<Person> people();            // see below
    static std::vector<Person> filter(std::vector<Person>, Predicate<Person>);
    static Predicate<Person> male;    // TBI
    static Predicate<Person> female;  // TBI
    static Predicate<Person> single;  // TBI
    static Predicate<Person> singleMale;
    static Predicate<Person> singleOrFemale;
};

// plausible implementation of equality for Person objects
bool operator==(Person left, Person right){
  return boost::iequals(left.getName(),right.getName());
}

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

typedef std::vector<Person> List;
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
  return list;
}


int main(int argc, char* argv[], char* envp[]){

  Person john2("John","Male","Married");

  auto people           = Person::people();
  auto males            = Person::filter(people, Person::male);
  auto females          = Person::filter(people, Person::female);
  auto singleMales      = Person::filter(people, Person::singleMale);
  auto singleOrFemales  = Person::filter(people, Person::singleOrFemale);

  std::cout << "Everyone:\t\t"          << people;
  std::cout << "\nNot John:\t\t";
  std::cout << "\nSingle or Female:\t"  << singleOrFemales;
  std::cout << "\nMales:\t\t\t"         << males;
  std::cout << "\nSingle Males:\t\t"    << singleMales;
  std::cout << "\nFemales:\t\t"         << females << std::endl;

  return 0;
}


