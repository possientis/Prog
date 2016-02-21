import java.io._

try {
  throw new NullPointerException
}
catch {
  case ex: IOException => println("Oops!")
  case ex: NullPointerException => println("Oops!!")
}
finally {
  println("finally ...")
}

val url =
try {
  throw new Exception
}
catch {
  case e: Exception => 45
}
finally{
  46  // this value is dropped, so 45 is value of exp
}

println(url)

def f(): Int = try {return 1} finally {return 2}
def g(): Int = try {1} finally {2}

println(f())  // 2
println(g()) // 1
