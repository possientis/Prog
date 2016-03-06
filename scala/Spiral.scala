import Element._

object Spiral {

  val space = elem(" ")

  val corner = elem("+")

  def spiral(nedges: Int, direction: Int): Element = {
    if (nedges == 1) elem("+")
    else {
      val sp = spiral(nedges - 1, (direction + 3) % 4)
      def verticalBar = elem('|', 1, sp.height)
      def horizontalBar = elem('-', sp.width, 1)
      if (direction == 0)
        (corner beside horizontalBar) above (sp beside space)
      else if (direction == 1)
        (sp above space) beside (corner above verticalBar)
      else if (direction == 2)
        (space beside sp) above (horizontalBar beside corner)
      else
        (verticalBar above corner) beside (space above sp)
    }
  }
 
  def main(args: Array[String]) = println(spiral(args(0).toInt, 0))
}
