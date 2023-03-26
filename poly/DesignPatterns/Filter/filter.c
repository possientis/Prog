// Filter design pattern
#include <stdio.h>
#include <assert.h>
#include <malloc.h>
#include <string.h>
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

//------------------------------------------------------------------------------
//                              Class Person
//------------------------------------------------------------------------------

typedef struct PersonData_ {
  int           count;          // reference counter
  const char*   name;
  const char*   gender;
  const char*   maritalStatus;
} PersonData;

typedef struct Person_ {
  PersonData *data;
} Person;

int Person_isNull(Person person){
  return person.data == NULL;
}

// accessor
const char* Person_name(Person person){
  assert(!Person_isNull(person));
  return person.data->name;
}

// accessor
const char* Person_gender(Person person){
  assert(!Person_isNull(person));
  return person.data->gender;
}

// accessor
const char* Person_maritalStatus(Person person){
  assert(!Person_isNull(person));
  return person.data->maritalStatus;
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

// some plausible implementation of equality
int Person_equals(Person left, Person right){
  assert(!Person_isNull(left));
  assert(!Person_isNull(right));
  return strcasecmp(Person_name(left),Person_name(right)) == 0;
}

//------------------------------------------------------------------------------
//                              Class Predicate
//------------------------------------------------------------------------------

typedef struct Predicate_ Predicate;
typedef struct PredicateData_ {
  int count;
  int (*test)(Predicate self, Person);  // virtual
  void (*delete)(Predicate self);       // virtual
} PredicateData;

typedef struct Predicate_ {
  PredicateData* data;
} Predicate;

typedef struct SimplePredicateData_ {   // inheritance
  PredicateData base;                   // just base object, no more data
} SimplePredicateData;

typedef struct OrPredicateData_ {       // inheritance
  PredicateData base;                   // base object has virtual test and delete
  Predicate left;                       // predicate defined by two operands which
  Predicate right;                      // are themselves predicates
} OrPredicateData;

typedef struct AndPredicateData_ {      // inheritance
  PredicateData base;                   // same structure as OrPredicate
  Predicate left;
  Predicate right;
} AndPredicateData;

typedef struct NotPredicate_ {          // inheritance
  PredicateData base;
  Predicate predicate;                  // predicate defined by opposit predicate
} NotPredicateData;

typedef struct EqualPredicateData_ {    // inheritance
  PredicateData base;
  Person person;                        // predicate defined by a person object
} EqualPredicateData;

// check for null reference
int Predicate_isNull(Predicate predicate){
  return predicate.data == NULL;
}

// copy for immutable objects, simply increase reference count
Predicate Predicate_copy(Predicate predicate){
  assert(!Predicate_isNull(predicate));
  predicate.data->count++;
  fprintf(stderr, 
      "Increasing reference count to %d of predicate with function %lx\n", 
      predicate.data->count, predicate.data->test);
  return predicate;
}

// virtual accessor
int Predicate_test(Predicate predicate, Person person){
  assert(!Predicate_isNull(predicate));
  assert(!Person_isNull(person));
  return predicate.data->test(predicate, person); // actual test in object data
}

// virtual destructor
void Predicate_delete(Predicate predicate){
  assert(!Predicate_isNull(predicate));
  assert(predicate.data->count > 0);
  predicate.data->count--;
  if(predicate.data->count == 0){
    void (*delete)(Predicate);
    delete = predicate.data->delete;              // actual delete in object data
    assert(delete != NULL);
    delete(predicate);
  }
  else{
    fprintf(stderr,
        "Decreasing reference count to %d of predicate with function %lx\n",
        predicate.data->count, predicate.data->test);
  }
}

// override
int OrPredicate_test(Predicate self, Person person){
  assert(!Predicate_isNull(self));
  assert(!Person_isNull(person));
  // downcasting self.data from (PredicateData*) to (OrPredicateData*)
  OrPredicateData* data = (OrPredicateData*) self.data;
  assert(data != NULL);
  Predicate leftPredicate = data->left;
  Predicate rightPredicate = data->right;
  assert(!Predicate_isNull(leftPredicate));
  assert(!Predicate_isNull(rightPredicate));
  if(Predicate_test(leftPredicate,person)){
    return 1;
  } else {
    return Predicate_test(rightPredicate, person);
  }
  assert(0);  // unreachable
}

// override
int AndPredicate_test(Predicate self, Person person){
  assert(!Predicate_isNull(self));
  assert(!Person_isNull(person));
  // downcasting self.data from (PredicateData*) to (OrPredicateData*)
  AndPredicateData* data = (AndPredicateData*) self.data;
  assert(data != NULL);
  Predicate leftPredicate = data->left;
  Predicate rightPredicate = data->right;
  assert(!Predicate_isNull(leftPredicate));
  assert(!Predicate_isNull(rightPredicate));
  if(!Predicate_test(leftPredicate,person)){
    return 0;
  } else {
    return Predicate_test(rightPredicate, person);
  }
  assert(0);  // unreachable
}

// override
int NotPredicate_test(Predicate self, Person person){
  assert(!Predicate_isNull(self));
  assert(!Person_isNull(person));
  // downcasting self.data from (PredicateData*) to (NotPredicateData*)
  NotPredicateData* data = (NotPredicateData*) self.data;
  assert(data != NULL);
  Predicate predicate = data->predicate;
  assert(!Predicate_isNull(predicate));
  return !Predicate_test(predicate, person);  // opposit to 'predicate'
}

// override
int EqualPredicate_test(Predicate self, Person person){
  assert(!Predicate_isNull(self));
  assert(!Person_isNull(person));
  // downcasting self.data from (PredicateData*) to (EqualPredicateData*)
  EqualPredicateData* data = (EqualPredicateData*) self.data;
  assert(data != NULL);
  Person reference = data->person;  // key defining data of predicate self
  assert(!Person_isNull(reference));
  return Person_equals(reference, person);
}

// argument for Predicate_simple
int male_test(Predicate self, Person person){
  assert(!Predicate_isNull(self));
  assert(!Person_isNull(person));
  return strcasecmp(Person_gender(person),"MALE") == 0;
}

// argument for Predicate_simple
int female_test(Predicate self, Person person){
  assert(!Predicate_isNull(self));
  assert(!Person_isNull(person));
  return strcasecmp(Person_gender(person),"FEMALE") == 0;
}

// argument for Predicate_simple
int single_test(Predicate self, Person person){
  assert(!Predicate_isNull(self));
  assert(!Person_isNull(person));
  return strcasecmp(Person_maritalStatus(person),"SINGLE") == 0;
}

// override
void SimplePredicate_delete(Predicate predicate){
  assert(!Predicate_isNull(predicate));
  assert(predicate.data->count == 0);  // should not be called otherwise
  SimplePredicateData* data = (SimplePredicateData*) predicate.data;
  fprintf(stderr,
      "Deallocating heap memory for SimplePredicate with function %lx\n",
      predicate.data->test);
  free(data);
}

// override
void OrPredicate_delete(Predicate predicate){
  assert(!Predicate_isNull(predicate));
  assert(predicate.data->count == 0); // should not be called otherwise
  OrPredicateData* data = (OrPredicateData*) predicate.data;  //downcast
  assert(data != NULL);
  Predicate leftPredicate = data->left;
  Predicate rightPredicate = data->right;
  fprintf(stderr,"Deallocating heap memory for OrPredicate\n");
  free(data);
  Predicate_delete(leftPredicate);
  Predicate_delete(rightPredicate);
}

// override
void AndPredicate_delete(Predicate predicate){
  assert(!Predicate_isNull(predicate));
  assert(predicate.data->count == 0); // should not be called otherwise
  AndPredicateData* data = (AndPredicateData*) predicate.data;  // downcast
  assert(data != NULL);
  Predicate leftPredicate = data->left;
  Predicate rightPredicate = data->right;
  fprintf(stderr,"Deallocating heap memory for AndPredicate\n");
  free(data);
  Predicate_delete(leftPredicate);
  Predicate_delete(rightPredicate);
}

// override
void NotPredicate_delete(Predicate predicate){
  assert(!Predicate_isNull(predicate));
  assert(predicate.data->count == 0); // should not be called otherwise
  NotPredicateData* data = (NotPredicateData*) predicate.data;  // downcast
  assert(data != NULL);
  Predicate opposit = data->predicate;
  fprintf(stderr,"Deallocating heap memory for NotPredicate\n");
  free(data);
  Predicate_delete(opposit);
}

// override
void EqualPredicate_delete(Predicate predicate){
  assert(!Predicate_isNull(predicate));
  assert(predicate.data->count == 0); // should not be called otherwise
  EqualPredicateData* data = (EqualPredicateData*) predicate.data;  // downcast
  assert(data != NULL);
  Person person = data->person;
  fprintf(stderr,"Deallocating heap memory for EqualPredicate with name %s\n",
      Person_name(person));
  free(data);
  Person_delete(person);
}

// factory method
Predicate Predicate_simple(int (*test)(Predicate, Person)){
  assert(test != NULL);
  fprintf(stderr,
      "Allocating heap memory for SimplePredicate with function  %lx\n", test);
  SimplePredicateData* data 
    = (SimplePredicateData*) malloc(sizeof(SimplePredicateData));
  assert(data != NULL);
  data->base.count = 1;
  data->base.test = test;
  data->base.delete = SimplePredicate_delete;
  Predicate predicate;
  predicate.data = (PredicateData*) data; // upcast
  return predicate;
}

// factory method
Predicate Predicate_or(Predicate left, Predicate right){
  assert(!Predicate_isNull(left));
  assert(!Predicate_isNull(right));
  fprintf(stderr, "Allocating heap memory for OrPredicate\n");
  OrPredicateData* data = (OrPredicateData*) malloc(sizeof(OrPredicateData));
  assert(data != NULL);
  data->base.count = 1;
  data->base.test = OrPredicate_test;
  data->base.delete = OrPredicate_delete;
  data->left = left;
  data->right = right;
  Predicate predicate;
  predicate.data = (PredicateData*) data; // upcast
  return predicate;
}

// factory method
Predicate Predicate_and(Predicate left, Predicate right){
  assert(!Predicate_isNull(left));
  assert(!Predicate_isNull(right));
  fprintf(stderr, "Allocating heap memory for AndPredicate\n");
  AndPredicateData* data = (AndPredicateData*) malloc(sizeof(AndPredicateData));
  assert(data != NULL);
  data->base.count = 1;
  data->base.test = AndPredicate_test;
  data->base.delete = AndPredicate_delete;
  data->left = left;
  data->right = right;
  Predicate predicate;
  predicate.data = (PredicateData*) data; // upcast
  return predicate;
}

// factory method
Predicate Predicate_not(Predicate predicate){
  assert(!Predicate_isNull(predicate));
  fprintf(stderr, "Allocating heap memory for NotPredicate\n");
  NotPredicateData* data = (NotPredicateData*) malloc(sizeof(NotPredicateData));
  assert(data != NULL);
  data->base.count = 1;
  data->base.test = NotPredicate_test;
  data->base.delete = NotPredicate_delete;
  data->predicate = predicate;
  Predicate opposit;
  opposit.data = (PredicateData*) data; // upcast
  return opposit;
}

// factory method
Predicate Predicate_isEqual(Person person){
  assert(!Person_isNull(person));
  fprintf(stderr,"Allocating heap memory for EqualPredicate with name %s\n",
      Person_name(person));
  EqualPredicateData* data 
    = (EqualPredicateData*) malloc(sizeof(EqualPredicateData));
  assert(data != NULL);
  data->base.count = 1;
  data->base.test = EqualPredicate_test;
  data->base.delete = EqualPredicate_delete;
  data->person = person;
  Predicate predicate;
  predicate.data = (PredicateData*) data; // upcast
  return predicate;
}

//------------------------------------------------------------------------------
//                              Class PersonList
//------------------------------------------------------------------------------

typedef struct PersonListData_ PersonListData;

typedef struct PersonList_ {
  PersonListData* data;
} PersonList;

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

// accesssor
Person PersonList_car(PersonList list){
  assert(!PersonList_isNull(list));
  return list.data->person;               // returns full ownership, no copy
}

// accessor
PersonList PersonList_cdr(PersonList list){
  assert(!PersonList_isNull(list));
  return list.data->next;                 // returns full ownership, no copy
}

// constructor
PersonList PersonList_new(Person person){
  assert(!Person_isNull(person));
  fprintf(stderr, "Allocating heap memory for list with name %s\n",
      Person_name(person));
  PersonListData* data = (PersonListData*) malloc(sizeof(PersonListData));
  assert(data != NULL);
  data->count = 1;                // first reference
  data->next = PersonList_null();
  data->person = person;          // new list takes ownership of Person, no copy
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

PersonList PersonList_cons(Person person, PersonList list){
  PersonList newList = PersonList_new(person);  // takes ownership of person
  assert(!PersonList_isNull(newList));
  newList.data->next = list;                    // takes ownership of list
  return newList;
}


PersonList PersonList_people(){

  Person bobby    = Person_new("Bobby","Male","Single");
  Person mike     = Person_new("Mike","Male","Single");
  Person diana    = Person_new("Diana","Female","Single");
  Person laura    = Person_new("Laura","Female","Married");
  Person john     = Person_new("John","Male","Married");
  Person robert   = Person_new("Robert","Male","Single");

  PersonList list1  = PersonList_new(bobby);          
  PersonList list2  = PersonList_cons(mike,   list1); 
  PersonList list3  = PersonList_cons(diana,  list2);
  PersonList list4  = PersonList_cons(laura,  list3);
  PersonList list5  = PersonList_cons(john,   list4);
  PersonList people = PersonList_cons(robert, list5);  

  // people has ownership of all previously allocated nodes and persons
  // hence there is no need to delete bobby,..,robert,list1,..,list5

  return people;
} 

void PersonList_print(PersonList list){
  if(!PersonList_isNull(list)){ // nothing to print otherwise
    Person person = PersonList_car(list);
    printf("(%s,%s,%s)\t",Person_name(person),Person_gender(person),
        Person_maritalStatus(person));
    PersonList_print(PersonList_cdr(list)); // recursive call
  }
}

PersonList PersonList_filter(PersonList list, Predicate predicate){
  assert(!Predicate_isNull(predicate));

  // recursion base case 
  if(PersonList_isNull(list)) return PersonList_null();

  // recursive call
  PersonList newList = PersonList_filter(PersonList_cdr(list),predicate);

  // adding current Person is it satisfies predicate
  Person person = PersonList_car(list);
  if(Predicate_test(predicate,person)){
    return PersonList_cons(Person_copy(person),newList);
  }
  else {
    return newList;
  }
}

//------------------------------------------------------------------------------
//                                  Main
//------------------------------------------------------------------------------

int main(int argc, char* argv[], char* envp[]){

  Person john2                = Person_new("John","Male","Single");

  Predicate male              = Predicate_simple(male_test);
  Predicate female            = Predicate_simple(female_test);
  Predicate single            = Predicate_simple(single_test);
  Predicate singleOrFemale    = Predicate_or(single, female); // takes ownership
  // copy required for ownership, to avoid deallocating 'single' twice
  Predicate singleMale        = Predicate_and(Predicate_copy(single), male);
  Predicate  isJohn           = Predicate_isEqual(john2);     // takes ownership
  Predicate  notJohn          = Predicate_not(isJohn);        // takes ownership

  PersonList people           = PersonList_people();
  PersonList males            = PersonList_filter(people, male);
  PersonList females          = PersonList_filter(people, female);
  PersonList singleMales      = PersonList_filter(people, singleMale);
  PersonList singleOrFemales  = PersonList_filter(people, singleOrFemale);
  PersonList notJohns         = PersonList_filter(people, notJohn);


  printf("Everyone:\t\t");          PersonList_print(people);
  printf("\nNot John:\t\t");        PersonList_print(notJohns);
  printf("\nSingle or Female:\t");  PersonList_print(singleOrFemales);
  printf("\nMales:\t\t\t");         PersonList_print(males);
  printf("\nSingle Males:\t\t");    PersonList_print(singleMales);
  printf("\nFemales:\t\t");         PersonList_print(females);
  printf("\n");

  // no garbage collection, explicit deallocation of top objects
  // Owned sub-objects are automatically deallocated in the process
  PersonList_delete(notJohns);
  PersonList_delete(singleOrFemales);
  PersonList_delete(singleMales);
  PersonList_delete(females);
  PersonList_delete(males);
  PersonList_delete(people);

  Predicate_delete(notJohn);
  Predicate_delete(singleMale);
  Predicate_delete(singleOrFemale);

  return 0;
}

