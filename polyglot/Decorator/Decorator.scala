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

trait ExtraCheese extends PlainPizza {
  override def description = super.description + " + extra cheese"
  override def cost        = super.cost + 0.5
}

trait ExtraOlives extends PlainPizza {
  override def description = super.description + " + extra olives"
  override def cost        = super.cost + 0.7
}

trait ExtraAnchovies extends PlainPizza {
  override def description = super.description + " + extra anchovies"
  override def cost        = super.cost + 0.8
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
