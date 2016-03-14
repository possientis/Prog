List(0,1,5) match { // pattern matching against a list of known size
  case List(0,_,_) => println("Found it!")
  case _           => println("what?")
}


List(0,2,4,1,4) match { // pattern matching against a list of arbitrary size
  case List(0, _*)  => println("Found it again!")
  case _            => println("hmmmm")
}


Array(0,3,5,6) match { // pattern matching against an array of aribitrary size
  case Array(0,3, _*) => println("I am so good at this!")
  case _              => println("jeez")
}

("hello", 10, true) match { // pattern matching against tuple
  case (word, idx, bool) => println("We have: " + word + ":" + idx + ":" + bool)
  case _                 => println("nope")
}

// cannot use 'Map' as you would 'List' or 'Array'
val m = Map('a'-> 1, 'b' -> 2, 'c' -> 5)

// however
m match {
  case x:Map[_, _]  => println("This works too!") 
  case _            => println("nah")
}

def generalSize(x: Any) = x match {
  case s:String     => s.length
  case m: Map[k,v]  => m.size       // lower case type variables work too
  case _            => -1           // not just Map[_,_]
}

println(generalSize("hello world!"))
println(generalSize(m))

def generalSize2(x: Any) = {
  if(x.isInstanceOf[String]){           // type checking
    val s = x.asInstanceOf[String]      // downcast
    s.length
  }
  else {
    if(x.isInstanceOf[Map[_,_]]){       // type checking
      val m = x.asInstanceOf[Map[_,_]]  // downcast
      m.size
    }
    else{
      -1
    }
  }
}

println(generalSize2("hello world!"))
println(generalSize2(m))

// this code generates unchecked warning
// warning: non variable type-argument Int in type pattern 
// Map[Int,Int] is unchecked since it is eliminated by erasure

def isIntIntMap(x: Any) = x match {
  case m: Map[Int,Int]  => true     // basically does not work
  case _                => false
}

println(isIntIntMap(Map(1->1,2->5)))      // true
// "possibly non-intuitive runtime behavior" ?????????????????
println(isIntIntMap(Map("abc" -> true)))  // true !!!!! hello?

// however, it works for Array and List
def isIntArray(x: Any) = x match {
  case a: Array[Int]  => true
  case _              => false
}


println(isIntArray(Array(1,2,3,4)))       // true
println(isIntArray(Array("abc","def")))   // false
println(isIntArray(Array(true,false)))    // false


