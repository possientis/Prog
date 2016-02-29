// abstract class
abstract class Element {
  def contents: Array[String] // no implementation, no 'abstract' modifier
  // use parameter-less method when there are no arguments and method 
  // does not change or depend on, mutable state.
  // ***********************************************************
  // uniform access principle: client code should not be affected 
  // by decision to implement attribute as field or as method 
  // ***********************************************************
  //
  // it is possible to remove 'def' and implement attributes as
  // fields. This can lead to faster code, but is less efficient
  // in space as each object needs to carry these fields. 
  // Reasons to choose fields over methods may change over time
  // and client code should not be impacted.
  //
  // client should not care whether implemented as field or as 
  // method, as long as the access function is pure, i.e.
  // does not have any side effects and does not depend on 
  // mutable state
  //
  // Java does not enforce uniform access principle
  // e.g. string.length() but array.length
  //
  // in scala, it is recommended to keep the '()' when
  // the method reads or writes mutable state
  //
  //  myString.length // no () because no side-effect
  //  out.println()   // better not to drop the ()
  
  def width: Int = if (height == 0) 0 else contents(0).length
  def height: Int = contents.length
}


