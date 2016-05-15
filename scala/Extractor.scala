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




