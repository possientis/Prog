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

  private def widen(w: Int): Element =
    if (w <= width) this
    else {
      val lpad = (w - width) / 2
      val rpad = w - (lpad + width)
      new ArrayElement(
        for (line <- contents)
        yield spaces(lpad) + line + spaces(rpad)
      )
    }
  // 'make' seems to trigger a deprecation warning
  private def spaces(n: Int) = new String(Array.make(n, ' '))

  def above(that: Element): Element = {
    val this1 = this widen that.width
    val that1 = that widen this.width
    // concatenation of two arrays
    new ArrayElement(this1.contents ++ that1.contents)
  }

  def display(): Unit = {
    for(line <- contents){
      println(line)
    }
  }

}

// if your class does not have an 'extends' clause, then
// it implicitely derives from AnyRef which corresponds to java.lang.Object
class ArrayElement(conts: Array[String]) extends Element {
  def contents: Array[String] = conts
//val contents: Array[String] = conts // possible to override a 'method' with a 'field' in scala
                                      // no need to change the abstract superclass.
// note that unlike java, scala forbids you to have a field and 
// method with the same name in the same class
}


val a1: Element = new ArrayElement(Array("Hello"))
val a2: Element = new ArrayElement(Array("World!!!!!"))
val a3 = a1 above a2
a3.display()


