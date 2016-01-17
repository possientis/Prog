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

typedef struct PersonData_ PersonData;
struct PersonData_ {
  int           count;          // reference counter
  const char*   name;
  const char*   gender;
  const char*   maritalStatus;
};

typedef struct Person_ Person;
struct Person_ {
  PersonData *data;
};

int Person_isNull(Person person){
  return person.data == NULL;
}

Person Person_new(const char* name, const char* gender, const char* maritalStatus){
  assert(name != NULL);
  assert(gender != NULL);
  assert(maritalStatus != NULL);
  fprintf(stderr,"Allocating heap memory for %s\n", name);
  PersonData *data = (PersonData*) malloc(sizeof(PersonData));
  assert(data != NULL);
  data->name = name;
  data->gender = gender;
  data->maritalStatus = maritalStatus;
  data->count = 1;          // first reference to heap allocated memory
  Person person;
  person.data = data;
  assert(!Person_isNull(person));
  return person;
}

Person Person_copy(Person person){
  assert(!Person_isNull(person));
  person.data->count++;
  fprintf(stderr, "Increasing reference count to %d for %s\n",
      person.data->count, person.data->name);
  return person;
}

void Person_delete(Person person ){
  assert(!Person_isNull(person));
  assert(person.data->count > 0);
  person.data->count--;
  if(person.data->count == 0){
    fprintf(stderr, "Deallocating heap memory for %s\n", person.data->name);
    free(person.data);
  }
  else{
    fprintf(stderr, "Decreasing reference count to %d for %s\n",
        person.data->count, person.data->name);
  }
}

const char* Person_name(Person person){
  assert(!Person_isNull(person));
  return person.data->name;
}

const char* Person_gender(Person person){
  assert(!Person_isNull(person));
  return person.data->gender;
}

const char* Person_maritalStatus(Person person){
  assert(!Person_isNull(person));
  return person.data->maritalStatus;
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

typedef struct PersonListData_ PersonListData;
typedef struct PersonList_ PersonList;
struct PersonList_ {
  PersonListData* data;
};

typedef struct PersonListData_ PersonListData;
struct PersonListData_ {
  int               count;
  Person            person;
  PersonList        next;
};

int PersonList_isNull(PersonList list){
  return list.data == NULL;
}

PersonList PersonList_null(){
  PersonList list;
  list.data = NULL;
  return list;
}

PersonList PersonList_new(Person person){
  assert(!Person_isNull(person));
  fprintf(stderr, "Allocating heap memory for list with name %s\n",
      Person_name(person));
  PersonListData* data = (PersonListData*) malloc(sizeof(PersonListData));
  assert(data != NULL);
  data->count = 1;                    // first reference
  data->next = PersonList_null();
  data->person = Person_copy(person); // increasing reference count 
  PersonList list;
  list.data = data;
  assert(!PersonList_isNull(list));
  return list;
}

PersonList PersonList_copy(PersonList list){
  if(PersonList_isNull(list)) return list;
  list.data->count++;
  fprintf(stderr, "Increasing reference count to %d for list with name %s\n",
      list.data->count, Person_name(list.data->person));
  return list;
}

void PersonList_delete(PersonList list){
  if(!PersonList_isNull(list)){ // nothing to do otherwise
    assert(list.data->count > 0);
    list.data->count--;
    if(list.data->count == 0){
      fprintf(stderr, "Deallocating heap memory for list with name %s\n",
          Person_name(list.data->person));
      Person_delete(list.data->person);
      PersonList_delete(list.data->next);
      free(list.data);
    } else{
      fprintf(stderr, "Decreasing reference count to %d for list with name %s\n",
          list.data->count, Person_name(list.data->person));
    }
  }
}

// accesssor
Person PersonList_car(PersonList list){
  assert(!PersonList_isNull(list));
  return Person_copy(list.data->person);  // increasing reference count
}

// accessor
PersonList PersonList_cdr(PersonList list){
  assert(!PersonList_isNull(list));
  return PersonList_copy(list.data->next);
}

PersonList PersonList_cons(Person person, PersonList list){
  PersonList newList = PersonList_new(person);
  assert(!PersonList_isNull(newList));
  newList.data->next = PersonList_copy(list);
  return newList;
}

PersonList PersonList_people(){
  Person robert   = Person_new("Robert","Male","Single");
  Person john     = Person_new("John","Male","Married");
  Person laura    = Person_new("Laura","Female","Married");
  Person diana    = Person_new("Diana","Female","Single");
  Person mike     = Person_new("Mike","Male","Single");
  Person bobby    = Person_new("Bobby","Male","Single");

  // careful with memory allocation/deallocation
  PersonList list1  = PersonList_new(bobby);
  PersonList list2  = PersonList_cons(mike,   list1);
  PersonList list3  = PersonList_cons(diana,  list2);
  PersonList list4  = PersonList_cons(laura,  list3);
  PersonList list5  = PersonList_cons(john,   list4);
  PersonList people = PersonList_cons(robert, list5);  

  return people;

} 

void PersonList_print(PersonList list){
  // TBI
}

PersonList PersonList_filter(PersonList people, Predicate p){
  // TBI
  return PersonList_copy(people);
}

int main(int argc, char* argv[], char* envp[]){

//  Person john2                = Person_new("John","Male","Single");

  PersonList people           = PersonList_people();
  PersonList males            = PersonList_filter(people, Person_male());
  PersonList females          = PersonList_filter(people, Person_female());
  PersonList singleMales      = PersonList_filter(people, Person_singleMale());
  PersonList singleOrFemales  = PersonList_filter(people, Person_singleOrFemale());
//  Predicate  isJohn           = Predicate_isEqual(john2);
//  Predicate  notJohn          = Predicate_not(isJohn);
//  PersonList notJohns         = PersonList_filter(people, notJohn);


  printf("Everyone:\t\t");          PersonList_print(people);
//  printf("\nNot John:\t\t");        PersonList_print(notJohns);
  printf("\nSingle or Female:\t");  PersonList_print(singleOrFemales);
  printf("\nMales:\t\t\t");         PersonList_print(males);
  printf("\nSingle Males:\t\t");    PersonList_print(singleMales);
  printf("\nFemales:\t\t");         PersonList_print(females);

  // no garbage collection
//  PersonList_delete(notJohns);
//  Predicate_delete(notJohn);
//  Predicate_delete(isJohn);
  PersonList_delete(singleOrFemales);
  PersonList_delete(singleMales);
  PersonList_delete(females);
  PersonList_delete(males);
  PersonList_delete(people);
//  Person_delete(john2);

  return 0;
}

