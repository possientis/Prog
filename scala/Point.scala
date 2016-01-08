class Point(val x: Double, val y: Double, addToGrid: Boolean = false){
  import Point._

  if(addToGrid) grid.add(this)
  
  def this() = this(0.0,0.0,true)

  def distanceToPoint(other: Point) = 
    distanceBetweenPoints(x, y, other.x, other.y)

  // apply is a special instance method: object.apply(...) is object(...)
  def apply(msg: String) = {
    println("point (" + x + "," + y + ") is saying %s" format msg)
  }
  
  // update is a special instance method: object.update(...) is object() = ... 
  def update(msg: String) = {
    println("point (" + x + "," + y + ") is saying %s" format msg)
  }
}

object Point {

  def main(args: Array[String]){
    val p1 = new Point(1.0, 2.2)
    val p2 = new Point(1.3, 5.5, true)
    val p3 = new Point(0.2, -2.4, false)
    val p4 = new Point()
    println("distance between p1 and p2 is: " + p1.distanceToPoint(p2))
    println("distance between p2 and p1 is: " + p2.distanceToPoint(p1))
    println("%d apples" format 5)
    p1("hello, how are you?")               // p1.apply(...)
    p2() = "Hello, I am well, thank you"    // p2.update(...)  
    
    println(Foo.bar)
    Foo.bar = 42
    println(Foo.bar)
    // {} or () is ok
    println(Vector.fill(4){math.random})
    println(Vector.fill(4)(math.random))
    val s = for {x <- 1 to 25 if x*x > 50}  yield 2*x
    println(s)

    val t = for {
      i <- 1 to 10
      j <- 1 to 10
      if i < j
    } yield (i,j)
    println(t)
    val u = for { (i,j) <- t if i > 5} yield i
    println(u)
    println(formatApples(10))
    println("Factorial(5) = %d" format factorial(5))
    val list = for(i <- 0 to 10) yield i.toDouble
    println(list map math.sqrt)
    
    lazy val x = {
      println("x is being evaluated")
      2*5}
    println("x = %d" format x)

    val list2 = 2::5::0::1::4::Nil
    println(qsort(list2))
    println(qsort2(list2))
    val list3 = List(0,1,2,3)
    val myNull = null
    val myNil = Nil
    println(myNull)
    println(myNil)

  }

  private val grid = new Grid()

  def distanceBetweenPoints(x1: Double, y1: Double, x2: Double, y2: Double) = {
    math.hypot(x1 - x2, y1 - y2)
  }

  def formatApples(x: Int) = "I ate %d apples".format(x)
  def factorial(x: Int): Int = 
    if(x == 0) 1 else x*factorial(x - 1)

  def qsort(list: List[Int]): List[Int] = list match {
    case Nil => Nil
    case pivot::tail =>
      val (smaller, rest) = tail.partition(_ < pivot)
      qsort(smaller) ::: pivot :: qsort(rest)
  }
  val qsort2: List[Int] => List[Int] = {
    case Nil => Nil
    case pivot::tail => 
      val (smaller, rest) = tail.partition(_ < pivot)
      qsort2(smaller) ::: pivot :: qsort2(rest)
  }
}


class Grid(){
  def add(p: Point){
    println("Grid::add is running (" + p.x + "," + p.y +")")
  }
}


trait FooLike { var bar: Int }
object Foo extends FooLike {
  private var x = 0
  def bar = {
    println("Foo::bar getter is running")
    x}
  def bar_=(value: Int){ x = value }
}


