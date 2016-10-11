// Filter design pattern

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

class Predicate[A](closure: A => Boolean) {
  def apply(a: A) = closure(a)
  def unary_!() = new Predicate[A](a => !this(a))
  def &(other: Predicate[A]) = 
    new Predicate[A](a => if(!this(a)) false else other(a))
  def |(other: Predicate[A]) = 
    new Predicate[A](a => if(this(a)) true else other(a))
}

object Predicate {
  def isEqual[A](targetRef: A): Predicate[A] = new Predicate(_ == targetRef)
}

class Person(val _name: String, val _gender: String, val _maritalStatus: String){

  // There is no real need to define getters, but here we go
  def name          = _name
  def gender        = _gender
  def maritalStatus = _maritalStatus

  // equals used by operator == 
  // check list of 'equals' overriding:
  // 1. having the right signature equals(other: Any): Boolean
  // 2. accompanying override for hashCode: x == y => x.hashCode == y.hashCode
  // 3. It is not defined in terms of mutable fields
  // 4. It defines an equivalence relation
  override def equals(other: Any) = other match {
    case p: Person  => name.equalsIgnoreCase(p.name)
    case _          => false
  } 
  // it is a sin to override 'equals' without overriding 'hashCode'
  override def hashCode = name.toUpperCase.hashCode  
  
  override def toString() = "("+ name +","+ gender +","+ maritalStatus +")"
}

// statics
object Person {

  // some static predicates
  val male    = new Predicate[Person](_.gender.equalsIgnoreCase("MALE"))
  val female  = new Predicate[Person](_.gender.equalsIgnoreCase("FEMALE"))
  val single  = new Predicate[Person](_.maritalStatus.equalsIgnoreCase("SINGLE"))
  val singleMale      = single & male
  val singleOrFemale  = single | female

  // sample of known persons
  def people: List[Person] =  {
    new Person("Robert","Male","Single")  ::
    new Person("John","Male","Married")   ::
    new Person("Laura","Female","Married")::
    new Person("Diana","Female","Single") ::
    new Person("Mike","Male","Single")    ::
    new Person("Bobby","Male","Single")   :: Nil
  }

  // printing list of people
  def printList(list: List[Person]) = {
    list.map(person => print(person + "\t"))
  }

  def filterList(list:List[Person], predicate:Predicate[Person]):List[Person] = {
    if(predicate == null) return list
    list.filter(predicate(_))
  }
}

object Filter {

  def main(args: Array[String]){
    val john2 = new Person("John","Male","Married")
    val notJohn: Predicate[Person] =  !Predicate.isEqual(john2)
    
    val people          = Person.people
    val males           = Person.filterList(people, Person.male)
    val females         = Person.filterList(people, Person.female)
    val singleMales     = Person.filterList(people, Person.singleMale)
    val singleOrFemales = Person.filterList(people, Person.singleOrFemale)
    val notJohns        = Person.filterList(people, notJohn)
    
    print("Everyone:\t\t");         Person.printList(people)
    print("\nNot John:\t\t");       Person.printList(notJohns)
    print("\nSingle or Female:\t"); Person.printList(singleOrFemales)
    print("\nMales:\t\t\t");        Person.printList(males)
    print("\nSingle Males:\t\t");   Person.printList(singleMales)
    print("\nFemales:\t\t");        Person.printList(females)
    print("\n")
  }
}

