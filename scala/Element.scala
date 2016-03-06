import Element.elem

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

  def above(that: Element): Element = {
    val this1 = this widen that.width
    val that1 = that widen this.width
    // concatenation of two arrays
    elem(this1.contents ++ that1.contents)
  }

  def beside(that: Element): Element = {
    val this1 = this heighten that.height
    val that1 = that heighten this.height
    /*
    val contents = new Array[String](this1.contents.length)
    for (i <- 0 until this1.contents.length)
      contents(i) = this1.contents(i) + that1.contents(i)
    new ArrayElement(contents)
    */
    elem( // look at this beauty  !
      for ((line1, line2) <- this1.contents zip that1.contents)
        yield line1 + line2
    )
  }

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
  private def heighten(h: Int): Element =
    if (h <= height) this
    else {
      val top = elem(' ', width, (h - height) / 2)
      var bot = elem(' ', width, h - height - top.height)
      top above this above bot
    }

  // 'make' seems to trigger a deprecation warning
  private def spaces(n: Int) = new String(Array.make(n, ' '))

  override def toString = contents mkString "\n"

}
// factory object allows to make class private
// if your class does not have an 'extends' clause, then
// it implicitely derives from AnyRef which corresponds to java.lang.Object
private class ArrayElement(conts: Array[String]) extends Element {
  def contents: Array[String] = conts
//val contents: Array[String] = conts // possible to override a 'method' with a 'field' in scala
                                      // no need to change the abstract superclass.
// note that unlike java, scala forbids you to have a field and 
// method with the same name in the same class
}

/*
class LineElement(s: String) extends Element {
  def contents = Array(s)
  override def width = s.length
  override def height = 1
}
*/


// factory object allows to make class private
// constructor of derived classes passes argument to constructor of superclass
private class LineElement(s: String) extends ArrayElement(Array(s)) {
  override def width = s.length
  override def height = 1
}

// factory object allows to make class private
private class UniformElement(
  ch: Char,
  override val width: Int,  // implements concrete methods of base class
  override val height: Int  // 'override' is required
) extends Element {
  private val line = new String(Array.make(width, ch))
  def contents = Array.make(height, line)
}

// companion object
object Element {
  // overloaded factory methods
  def elem(contents: Array[String]): Element =
    new ArrayElement(contents)
  def elem(chr: Char, width: Int, height: Int): Element =
    new UniformElement(chr, width, height)
  def elem(line: String): Element =
    new LineElement(line)
}

/*

val a1: Element = Element.elem(Array("Hello"))
val a2: Element = Element.elem(Array("World!!!!!"))
val a3 = a1 above a2
println(a3)

println((Array(1,2,3) zip Array("a","b","c")).mkString(", "))

*/

