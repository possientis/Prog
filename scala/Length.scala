object Length {

  def length[A](list: List[A]): Int = {
    if(list.isEmpty) 0
    else 1 + length(list.tail)
  }
  
  def length2[A](list: List[A]): Int = list match {
    case _ :: tail => 1 + length2(tail)
    case Nil       => 0
  }

  def main(args: Array[String]){
   
    println(length(Nil)) 
    println(length2(Nil)) 
    
    val x = 1 :: 2 :: 3 :: 4 :: Nil
    println(length(x))
    println(length2(x))
    
  }
}
