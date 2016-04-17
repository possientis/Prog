trait Abstract {
  type T                  // abstract type
  def transform(x: T): T  // abstract method
  val initial: T          // abstract field (value)
  var current: T          // abstract field
}


class Concrete extends Abstract {
  type T = String
  def transform(x: String) = x + x
  val initial = "hi"
  var current = initial
}
  
// an abstract 'val' provides a guarantee of immutability. It cannot
// be implemented by a 'var' or a 'def' in concrete subclass, whereas
// an abstract 'def' *can* be implemented by a 'val'

abstract class A {
  val v: String   // 'v' for value
  def m: String   // 'm' for method
}

class C1 extends A {
  val v: String = "abc"
  val m: String = "def"   // Ok to override a 'def' with a 'val'
}

class C2 extends A {
//  def v: String = "abc"   // ERROR: cannot override a 'val' with a 'def'
  val v = "oh well..."
  def m: String = "def"
}


trait AbstractTime1 {
  var hour: Int
  var minute: Int
}

// equivalent to 

trait AbstractTime2 {
  def hour: Int       // getter for 'hour'
  def hour_=(x:Int)   // setter for 'hour'
  def minute: Int     // getter for 'minute'
  def minute_=(x:Int) // setter for 'minute'
}

// what is the point of abstract type?
class Food{}
abstract class Animal1 {
  def eat(food:Food)
}


class Grass extends Food {}
class Cow1 extends Animal1 {
//  override def eat(food:Grass) = {} // ERROR: eat is suppose to accept 'Food', not just 'Grass'
  def eat(food:Food) = {}             // 'override' seems optional
}

// what food is 'suitable' cannot be determined at the level of Animal2
abstract class Animal2 {
  type SuitableFood <: Food           // asbtract type: declared as subtype of Food (it has an upper bound)
  def eat(food: SuitableFood)
}

class Cow2 extends Animal2 {
  type SuitableFood = Grass
  def eat(food: Grass) = {}           // Ok now
}





















