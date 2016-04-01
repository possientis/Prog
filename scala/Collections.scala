// SEQUENCE TYPES

// array, type Array
val numbers = new Array[Int](5) // type and length

println(numbers(3))             // random access with parantheses, not square brackets

//initial value: 0 for numeric types, false for booleans and null for reference types

numbers(3) = 42
println(numbers(3))             // 42
numbers.update(3,420)           // numbers(3) = 420, update akin to C++ operator=
println(numbers(3))             // 420

for(x <- numbers)
  println(x)

// if you need index as you loop through
for(i <- 0 until numbers.length)  // until excludes bound
  println(i + " " + numbers(i))

for(i <- 0 to numbers.length - 1) // without until
  println(i + " " + numbers(i))

val words = "The quick brown fox".split(" ")
println(words)                    // [Ljava.lang.String;@69e1968d
for(w <- words) println(w)

// array buffer, type ArrayBuffer
// you can add and remove elements at the beginning and end
// addition and removal are O(1) amortized
// need to import from mutable collection package
import scala.collection.mutable.ArrayBuffer

val buf = new ArrayBuffer[Int]()  // no need for size, implementation will adjust

// append to buffer with +
buf += 12
buf += 15
println(buf) // ArrayBuffer(12, 15)
for(x <- buf) println(x)
// usual array methods are available
println(buf.length) // 2
println(buf(0))     // 12
buf(0) = 16
println(buf(0))     // 16
buf.update(0,17)
println(buf(0))     // 17

// list
// the usual immutable data structure of functional programming languages
val arr = buf.toArray // conversion
println(arr)          // [I@49336bd

val list = buf.toList
println(list)         // List(17, 15)

// tuples
val tuple1 = (1, "hello", Console)  // fixed size but different types allowed
// tuples do not inherit from Collection (due to the multiple types)
// main use -> function returning multiple values

def longestWord(words: Array[String]) = {
  var word = words(0)
  var idx  = 0
  for(i <- 0 until words.length){
    if(words(i).length > word.length){
      word = words(i)
      idx = i
    }
  }
  (word, idx)
}    

val longest = longestWord(words)
println(longest)    // (quick,1)
println(longest._1) // quick  , fst in haskell, longest[0] in python
println(longest._2) // 1, snd in haskell, longest[1] in python

// variable binding
val (word, idx) = longest
println(word)  // quick
println(idx)    // 1

// warning !!
val word2, idx2 = longest
println(word2)  // (quick, 1)
println(idx2)   // (quick, 1)



