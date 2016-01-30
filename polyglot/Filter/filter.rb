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

class Predicate
  def initialize(closure)
    @test = closure
  end
  def test(person)
    return @test.call(person)
  end
  def self.isEqual(targetRef)
    return Predicate.new(lambda {|person| person == targetRef})
  end
  def !()
    return Predicate.new(lambda {|person| !test(person)})
  end
  def &(other) 
    return Predicate.new(lambda {|person| !test(person)?false:other.test(person)})
  end
  def |(other) 
    return Predicate.new(lambda {|person| test(person)?true:other.test(person)})
  end
end

class Person

  def initialize(name,gender,maritalStatus)
    @name, @gender, @maritalStatus = name, gender, maritalStatus
  end 

  # like Python or C#, Ruby has property idioms. Let's use them.
  # The following line automatically generates default getter methods
  attr_reader :name, :gender, :maritalStatus 
  # However these getter methods can be customized by changing code below 
  def name() return @name end
  def gender() return @gender end
  def maritalStatus() return @maritalStatus end

  # possible equality
  def ==(other)
    if other.class == Person
      return name.casecmp(other.name) == 0
    else
      return false
    end
  end
 
  # string representation
  def to_s()
    return "(#{name},#{gender},#{maritalStatus})"
  end

  # some static predicates
  @@male = Predicate.new(lambda {|p| p.gender.casecmp("MALE") == 0})
  @@female = Predicate.new(lambda {|p| p.gender.casecmp("FEMALE") == 0})
  @@single = Predicate.new(lambda {|p| p.maritalStatus.casecmp("SINGLE") == 0})
  @@singleMale = @@single & @@male
  @@singleOrFemale = @@single | @@female

  # accessors for static predicates
  def self.male() return @@male end
  def self.female() return @@female end
  def self.single() return @@single end
  def self.singleMale() return @@singleMale end
  def self.singleOrFemale() return @@singleOrFemale end
  
  # sample list of people
  def self.people()
    return [Person.new("Robert","Male","Single"),
            Person.new("John","Male","Married"),
            Person.new("Laura","Female","Married"),
            Person.new("Diana","Female","Single"),
            Person.new("Mike","Male","Single"),
            Person.new("Bobby","Male","Single")]
  end

  # printing list of people
  def self.printList(list)
    list.map {|person| print "#{person}\t"}
  end

  # Ruby supports a filter method called 'select'
  def self.filterList(list, predicate)
    if predicate == nil then return list end
    return list.select {|person| predicate.test(person)}
  end

end


john2 = Person.new("John","Male","Married")
notJohn = !Predicate.isEqual(john2)

people          = Person.people
males           = Person.filterList(people, Person.male)
females         = Person.filterList(people, Person.female)
singleMales     = Person.filterList(people, Person.singleMale)
singleOrFemales = Person.filterList(people, Person.singleOrFemale)
notJohns        = Person.filterList(people,notJohn)

print "Everyone:\t\t";          Person.printList(people)
print "\nNot John:\t\t";        Person.printList(notJohns)
print "\nSingle or Female:\t";  Person.printList(singleOrFemales)
print "\nMales:\t\t\t";         Person.printList(males)
print "\nSingle Males:\t\t";    Person.printList(singleMales)
print "\nFemales:\t\t";         Person.printList(females)
print("\n")

