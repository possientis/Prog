// a first faulty design of class Currency

abstract class Currency1 {
  val amount: Long
  def designation: String
  override def toString = amount + " " + designation  
//  def +(that:Currency):Currency = {...}
//  def *(x: Double): Currency =  {...}
}


// a second (still imperfect) design
abstract class AbstractCurrency {
  type Currency <: AbstractCurrency
  val amount: Long
  def designation: String
  override def toString = amount + " " + designation
//  def +(that: Currency): Currency = ...
//  def *(x: Double): Currency = ...
}



