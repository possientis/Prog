type Environment = String => Int

object Tree{
  def main(args: Array[String]){
  }
}

abstract class Tree
case class Sum(l:Tree, r:Tree) extends Tree
case class Var(n:String) extends Tree
case class Const(v: Int) extends Tree


