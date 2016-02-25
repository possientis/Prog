// this function is not tail-recursive
def boom(x: Int): Int =
  if (x == 0) throw new Exception("boom!")
 else boom(x - 1) + 1


//boom(5) // look at stack trace

// this function is tail-recursive
def bang(x: Int): Int =
  if (x == 0) throw new Exception("boom!")
 else bang(x - 1)

bang(5)

// no tail-call optimization by compiler in this case
val funValue = nestedFun _
def nestedFun(x: Int) {
  if (x != 0) { println(x); funValue(x - 1) }
}


