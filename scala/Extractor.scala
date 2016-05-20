/*
This is where Scala’s extractors come in: They
let you define new patterns for pre-existing types, where the pattern need not
follow the internal representation of the type.
*/


/*
An extractor in Scala is an object that has a method called unapply as one of
its members. The purpose of that unapply method is to match a value and
take it apart. Often, the extractor object also defines a dual method apply for
building values, but this is not required.
*/

/* 
One big advantage of extractors v case classes: they break the link between data
representations and patterns. So you can hide implementation choices.
if client code only uses extractors, you are free to change implementation of
objects, as long as you update extractors accordingly.
Case classes have advantages of their own though:
1. much easier to define, less verbose
2. more efficient code
3. if base class is sealed, compiler will check exhaustiveness of pattern matches.


so which one to choose? If you do not know, choose case classes. you can always replace
them by extractors later, so client code will still work.
*/

// good design: keep the 'duality' between apply and unapply (but not enforced by scala")
object EMail {  // an extractor

  /** The injection method (optional) */
  def apply(user: String, domain: String) = user+"@"+domain // optional

  /** The extraction method (mandatory) */
  def unapply(email: String): Option[(String, String)] = {
    val parts = email split "@"
    if (parts.length == 2) Some(parts(0), parts(1)) else None
  }
}

/*
The apply method
has the same meaning as always: It turns EMail into a function ob-
ject. So you can write EMail("John", "epfl.ch") to construct the string
"John@epfl.ch"
*/

println(EMail("John","epfl.ch"))

println(EMail.unapply("John@epfl.ch"))  // Some((John,epfl.ch))
println(EMail.unapply("John Doe"))      // None

// there is no such thing as a one dimensional tuple in scala
// simply return value wrapped in a 'Some' 
object Twice {
  def apply(s: String) = s + s
  def unapply(s: String) = {
    val l = s.length / 2
    val half = s.substring(0, l)
    if (half == s.substring(l)) Some(half) else None
  }
}

// It’s also possible that an extractor pattern does not bind any variables. In
// that case the corresponding unapply method returns a boolean— true for
// success and false for failure.

// you cannot defined an 'apply' method in this case
object UpperCase {
  def unapply(s: String) = s.toUpperCase == s
}

def test2(s:String) = s match {
  case EMail(Twice(x @ UpperCase()), domain) => // do not forget '()' in 'UpperCase'
    "match: " + x + " in domain " + domain
  case _ => "no match"
}

println(test2("DIDI@hotmail.com"))  // match: DI in domain hotmail.com
println(test2("DIDO@hotmail.com"))  // no match
println(test2("didi@hotmail.com"))  // no match


// Seq[T] is common superclass to List[T], Array[T] and others
object Domain {
//  def apply(parts: String*): String = // variable length argument
//    parts.reverse.mkString(".")
  def unapplySeq(whole: String): Option[Seq[String]] =
    Some(whole.split("\\.").reverse)  // takes a regex as argument
}

def isTomInDotCom(s:String) = s match {
  // Email has unapply method which is applied to argument s
  // it returns a pair (a,b) wrapped in a 'Some'. a is compared 
  // to "tom" while b is compared to Domain("com", _*). Domain 
  // has unapplySeq method which is applied to argument b. 
  // It returns a Seq[String] wrapped in a 'Some'. The Seq
  // is then matched against ("com", _*) 
  case EMail("tom", Domain("com", _*))  => true
  case _                                => false
}

println("isTom...")
println(isTomInDotCom("tom@sun.com"))         // true
println(isTomInDotCom("peter@sun.com"))       // false
println(isTomInDotCom("tom@acm.org"))         // false
println(isTomInDotCom("tom@host1.yahoo.com")) // true

object ExpandedEMail {
  def unapplySeq(email: String) : Option[(String, Seq[String])] = {
    val parts = email split "@"
      if (parts.length == 2)
        Some(parts(0), parts(1).split("\\.").reverse)
      else
        None
  }
}

val s = "tom@support.epfl.ch"
val ExpandedEMail(name,topdomain, subdomains @ _*) = s

println(name)
println(topdomain)
println(subdomains)



















