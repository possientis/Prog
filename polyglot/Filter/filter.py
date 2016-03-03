# Filter design pattern

# This pattern allows to use a list of objects and perform
# a filtering operation on that list so as to obtain a new
# list comprised of those objects in the initial list which
# satisfy a given predicate. Since the introduction of
# lambda expressions within Java 8 and the introduction
# of functional interfaces such as Predicate<T>, this 
# pattern is not very useful in practice and amounts 
# mainly to a coding exercise aiming at re-implementing
# the Predicate<T> java interface. This pattern is not
# useful either in functional languages which directly 
# support first class functions and filter operations on lists.


class Predicate(object):
    def __init__(self,closure):
        self._test = closure

    def __call__(self,person):
        return self._test(person)
    
    def isEqual(targetRef):
        return Predicate(lambda p: p == targetRef)

    def __invert__(self):       # unary operator '~'
        return Predicate(lambda p: not self(p))

    def __and__(self, other):   # binary operator '&' 
        return Predicate(lambda p: False if not self(p) else other(p))

    def __or__(self, other):   # binary operator '|' 
        return Predicate(lambda p: True if self(p) else other(p))

class Person(object):
    def __init__(self,name,gender,maritalStatus):
        self._name           = name
        self._gender         = gender
        self._maritalStatus  = maritalStatus

    # like C# or Ruby, Python has property idioms. Let's use them.
    @property
    def name(self):
        return self._name
    @property
    def gender(self):
        return self._gender
    @property
    def maritalStatus(self):
        return self._maritalStatus
    # possible equality
    def __eq__(self,other):
        if isinstance(other,Person):
            return self.name.upper() == other.name.upper()
        else:
            return false

    # string representation
    def __repr__(self):
        return "(" + self.name + "," + self.gender + "," + self.maritalStatus + ")"

    # some static predicates
    male            = Predicate(lambda p: p.gender.upper() == "MALE") 
    female          = Predicate(lambda p: p.gender.upper() == "FEMALE") 
    single          = Predicate(lambda p: p.maritalStatus.upper() == "SINGLE") 
    singleMale      = single & male
    singleOrFemale  = single | female
    
    # sample of known people
    def people():
        return [Person("Robert","Male","Single"),
                Person("John","Male","Married"),
                Person("Laura","Female","Married"),
                Person("Diana","Female","Single"),
                Person("Mike","Male","Single"),
                Person("Bobby","Male","Single")]
    
    # printing list of people
    def printList(people):
        for person in people:
            print(person, end = "\t")

    # various way to filter in python 
    def filterList(people,predicate):
        if predicate == None: return people
        # using python list comprehension
        def filter1(people, predicate):
            return [x for x in people if predicate(x)]
        # don't even need 'lambda p: predicate(p)'
        def filter2(people, predicate):
            return filter(predicate, people)
        # using a generator
        def filter3(people, predicate):
            for person in people:
                if predicate(person): yield person
        # choose here
        return filter3(people,predicate)


john2 = Person("John","Male","Married")
notJohn = ~Predicate.isEqual(john2)


people              = Person.people()
males               = Person.filterList(people, Person.male)
females             = Person.filterList(people, Person.female)
singleMales         = Person.filterList(people, Person.singleMale)
singleOrFemales     = Person.filterList(people, Person.singleOrFemale)
notJohns            = Person.filterList(people, notJohn)

print("Everyone:", end = "\t\t");          Person.printList(people);
print("\nNot John:", end = "\t\t");        Person.printList(notJohns);
print("\nSingle or Female:", end = "\t");  Person.printList(singleOrFemales);
print("\nMales:", end = "\t\t\t");         Person.printList(males);
print("\nSingle Males:", end = "\t\t");    Person.printList(singleMales);
print("\nFemales:", end = "\t\t");         Person.printList(females);
print("")
