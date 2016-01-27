object Traits {
  def main(args: Array[String]){
    println("This is running")
    val xy = new AnyRef with X with Y
    val yx = new AnyRef with Y with X
    println(xy.a) // Y.a then X.a then A.a
    println("and now ...")
    println(yx.a) // X.a then Y.a then A.a
  }
}

trait A{
    def a = 1
}

trait X extends A{
    override def a = {
        println("X")
        super.a
    }
}  


trait Y extends A{
    override def a = {
        println("Y")
        super.a
    }
}

