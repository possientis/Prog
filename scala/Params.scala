// variadic function

object Params {
  def main(args: Array[String]){  // do not use String* for main
    echo("abc","def","ghi")   // variable number of arguments

    val arr = Array("abc","def","ghi")
    // you cannot call echo with array argument directly
    //  echo(arr)  // type mismatch
    // but this will work
    echo(arr:_*)
  }

  // argument packaged as Array[String] inside body of function
  def echo(args: String*) = for(arg <- args) println (arg)
}
