// Filter design pattern
#include <stdio.h>
#include <assert.h>
#include <malloc.h>
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

typedef struct PersonImpl_ PersonImpl;
struct PersonImpl_ {
  int count;
  const char* name;
  const char* gender;
  const char* maritalStatus;
};

typedef struct Person_ Person;
struct Person_ {
  PersonImpl *impl;
};

Person Person_new(const char* name, const char* gender, const char* maritalStatus){
  // TBI
  assert(name != NULL);
  assert(gender != NULL);
  assert(maritalStatus != NULL);
  fprintf(stderr,"Allocating heap memory for %s\n", name);
  PersonImpl *impl = (PersonImpl*) malloc(sizeof(PersonImpl));
  assert(impl != NULL);
  impl->name = name;
  impl->gender = gender;
  impl->maritalStatus = maritalStatus;
  impl->count = 1;          // first reference to heap allocated memory
  Person person;
  person.impl = impl;
  return person;
}

Person Person_copy(Person person){
  assert(person.impl != NULL);
  person.impl->count++;
  return person;
}

void Person_delete(Person person ){
  assert(person.impl != NULL);
  assert(person.impl->count > 0);
  person.impl->count--;
  if(person.impl->count == 0){
    fprintf(stderr, "Deallocating heap memory for %s\n", person.impl->name);
    free(person.impl);
  }
}


typedef struct Predicate_ Predicate;
struct Predicate_ {
};

void Predicate_delete(Predicate p){
  // TBI
}

Predicate Predicate_isEqual(Person person){
  // TBI
  Predicate temp;
  return temp;
}

Predicate Predicate_not(Predicate p){
  // TBI
  Predicate temp;
  return temp;
}



Predicate Person_male()           {Predicate temp; return temp;} // TBI
Predicate Person_female()         {Predicate temp; return temp;} // TBI
Predicate Person_singleMale()     {Predicate temp; return temp;} // TBI
Predicate Person_singleOrFemale() {Predicate temp; return temp;} // TBI

typedef struct PersonListImpl_ PersonListImpl;
struct PersonListImpl_ {
  Person            person;
  PersonListImpl*   next;
};

typedef struct PersonList_ PersonList;
struct PersonList_ {
  PersonListImpl* impl;
};

PersonList PersonList_new(){
  PersonList list;
  list.impl = NULL;
  return list;
}

void PersonList_delete(PersonList list){
  
}

int PersonList_isNull(PersonList list){
  return (list.impl == NULL);
}

Person PersonList_car(PersonList list){
  assert(list.impl != NULL);
  return list.impl->person;
}

PersonList PersonList_cdr(PersonList list){
  assert(list.impl != NULL);
  PersonList temp;
  temp.impl = list.impl->next;
  return temp;
}


PersonList PersonList_people(){
  // TBI
  PersonList_new();
} 

void PersonList_print(PersonList list){
  // TBI
}

PersonList PersonList_filter(PersonList people, Predicate p){
  // TBI
  return people;
}

int main(int argc, char* argv[], char* envp[]){

  Person john2                = Person_new("John","Male","Single");
  PersonList people           = PersonList_people();
  PersonList males            = PersonList_filter(people, Person_male());
  PersonList females          = PersonList_filter(people, Person_female());
  PersonList singleMales      = PersonList_filter(people, Person_singleMale());
  PersonList singleOrFemales  = PersonList_filter(people, Person_singleOrFemale());
  Predicate  isJohn           = Predicate_isEqual(john2);
  Predicate  notJohn          = Predicate_not(isJohn);
  PersonList notJohns         = PersonList_filter(people, notJohn);


  printf("Everyone:\t\t");          PersonList_print(people);
  printf("\nNot John:\t\t");        PersonList_print(notJohns);
  printf("\nSingle or Female:\t");  PersonList_print(singleOrFemales);
  printf("\nMales:\t\t\t");         PersonList_print(males);
  printf("\nSingle Males:\t\t");    PersonList_print(singleMales);
  printf("\nFemales:\t\t");         PersonList_print(females);

  // no garbage collection
  PersonList_delete(notJohns);
  Predicate_delete(notJohn);
  Predicate_delete(isJohn);
  PersonList_delete(singleOrFemales);
  PersonList_delete(singleMales);
  PersonList_delete(females);
  PersonList_delete(males);
  PersonList_delete(people);
  Person_delete(john2);

  return 0;
}

