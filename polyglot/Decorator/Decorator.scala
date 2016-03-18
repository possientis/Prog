// Decorator Design Pattern

// The implementation of the decorator pattern in scala does not follow
// the pattern encountered in other languages, due to scala built in 'traits'

trait Pizza {
  def description : String;
  def cost : Double;
}

class PlainPizza extends Pizza {
  override def description = "Plain pizza"
  override def cost        = 3.0
}

// 'abstract override' is very surprising. The keyword abstract is in fact
// required as the call to 'super' formally looks like a call to the trait Pizza
// However, we shall use these traits with concrete implementation of Pizza.

trait ExtraCheese extends Pizza {
  abstract override def description = super.description + " + extra cheese"
  abstract override def cost        = super.cost + 0.5
}

trait ExtraOlives extends Pizza {
  abstract override def description = super.description + " + extra olives"
  abstract override def cost        = super.cost + 0.7
}

trait ExtraAnchovies extends Pizza {
  abstract override def description = super.description + " + extra anchovies"
  abstract override def cost        = super.cost + 0.8
}

object Decorator {

  def main(args: Array[String]) = {

    val plainPizza  
      = new PlainPizza

    val nicePizza   
      = new PlainPizza with ExtraCheese

    val superPizza  
      = new PlainPizza with ExtraCheese with ExtraOlives

    val ultraPizza  
      = new PlainPizza with ExtraCheese with ExtraOlives with ExtraAnchovies

    println(
      "Plain Pizza: "   +
      "\tCost: "        + plainPizza.cost
    + "\tDescription: " + plainPizza.description)

    println(
      "Nice Pizza: "   +
      "\tCost: "        + nicePizza.cost
    + "\tDescription: " + nicePizza.description)

    println(
      "Super Pizza: "   +
      "\tCost: "        + superPizza.cost
    + "\tDescription: " + superPizza.description)

    println(
      "Ultra Pizza: "   +
      "\tCost: "        + ultraPizza.cost
    + "\tDescription: " + ultraPizza.description)
  }
}
