// XML is often more convenient than strings  to serialize objects.
// it is easier to parse...
// XML is more convenient than raw object data: if you need to change
// the data model, you simply need to adjust the parser somewhat.

println("I am now running..")

// built-in support for xml literal, the compiler understands
val x = 
<a> 
  This is xml. 
  Here is a tag: <atag/>
</a>

println(x)
/*
<a> 
  This is xml. 
  Here is a tag: <atag></atag>
</a>
*/

// XML node with tag 'a' is of class 'Elem'
println(x.getClass()) // class scala.xml.Elem

// class 'Node' is abstract super class of all XML subclasses
// class 'Text' is a node holding just text, .e.g. the 'stuff' in <a>stuff</a>
// class 'NodeSeq' holds a sequence of nodes. (actually looks like Node <: NodeSeq )

// use {} to insert xml which is computed at run time:
val y = <a> 2 + 2 = {2+2} </a>
println(y)  // <a> 2 + 2 = 4 </a>

// you can nest the '{}' as much as you want
val yearMade = 1955
val z = <a> {if (yearMade < 2000) <old>{yearMade}</old>
             else xml.NodeSeq.Empty}
        </a>
println(z)
// <a> <old>1955</old> 
//         </a>

// Any '<' '/' '>' in the text will be escaped, if you print the
// node back out
val x1 = <a> {"</a>potential security holes<a>"}</a>
println(x1) // <a> &lt;/a&gt;potential security holes&lt;a&gt;</a>

// XML literal plus {} escapes make it easy to write conversions
// from internal data structures to XML.

// database of Coca-cola thermometers...

abstract class CCTherm {
  val description: String
  val yearMade: Int
  val dateObtained: String
  val bookPrice: Int  // in pennies
  val purchasePrice: Int // in pennies
  val condition: Int    // 1-10
  override def toString = description
  def toXML =
    <cctherm>
      <description>{description}</description>
      <yearMade>{yearMade}</yearMade>
      <dateObtained>{dateObtained}</dateObtained>
      <bookPrice>{bookPrice}</bookPrice>
      <purchasePrice>{purchasePrice}</purchasePrice>
      <condition>{condition}</condition>
    </cctherm>

}

val therm = new CCTherm {
  val description   = "hot dog thermometer"
  val yearMade      = 1952
  val dateObtained  = "March 14, 2006"
  val bookPrice     = 2199
  val purchasePrice = 500 // sucker !
  val condition     = 9
}

println(therm)  // hot dog thermometer
println(therm.toXML)

/*
<cctherm>
      <description>hot dog thermometer</description>
      <yearMade>1952</yearMade>
      <dateObtained>March 14, 2006</dateObtained>
      <bookPrice>2199</bookPrice>
      <purchasePrice>500</purchasePrice>
      <condition>9</condition>
    </cctherm>
*/
// you escape '{' and '}' within xml text with {{ and }}.
val x2 = <a> }}}} brace yourself! {{{{ </a>
println(x2) // <a> }} brace yourself! {{ </a>

// text
println(<a>blah blah <tag/>blah</a>.text)   // blah blah blah
println(<a>input ---&gt; output </a>.text)  // input ---> output

// sub-element
println(<a><b><c>hello</c></b></a> \ "b")   // <b><c>hello</c></b>
println(<a><b><c>hello</c></b></a> \ "c")   // ""
// sub-element (deep search)
println(<a><b><c>hello</c></b></a> \\ "c")   // <c>hello</c>

val joe = <employee name="Joe" rank="code monkey" serial="123"/>

println(joe \ "@name")    // Joe
println(joe \ "@rank")    // code monkey
println(joe \ "@serial")  // 123

def fromXML(node: xml.Node): CCTherm =
  new CCTherm {
    val description   =                  (node \ "description").text
    val yearMade      = Integer.parseInt((node \ "yearMade").text)
    val dateObtained  =                  (node \ "dateObtained").text
    val bookPrice     = Integer.parseInt((node \ "bookPrice").text)
    val purchasePrice = Integer.parseInt((node \ "purchasePrice").text)
    val condition     = Integer.parseInt((node \ "condition").text)
  }

println(fromXML(therm.toXML)) // hot dog thermometer

// using toString() to serialize xml is not safe as the resulting string
// does not include a description of the character encoding
val node = therm.toXML
xml.XML.save("therm1.xml", node, "UTF-8", true, null)
// file therm1.xml looks like this:
/*
<?xml version='1.0' encoding='UTF-8'?>
<cctherm>
      <description>hot dog thermometer</description>
      <yearMade>1952</yearMade>
      <dateObtained>March 14, 2006</dateObtained>
      <bookPrice>2199</bookPrice>
      <purchasePrice>500</purchasePrice>
      <condition>9</condition>
    </cctherm>
*/

val loadnode = xml.XML.loadFile("therm1.xml")
println(loadnode)
/*
<cctherm>
      <description>hot dog thermometer</description>
      <yearMade>1952</yearMade>
      <dateObtained>March 14, 2006</dateObtained>
      <bookPrice>2199</bookPrice>
      <purchasePrice>500</purchasePrice>
      <condition>9</condition>
    </cctherm>
*/
println(loadnode == node) // false

// XML PATTERNS
// an XML pattern looks just like an XML literal. The main difference
// is that if you insert a {} escape, then the cose inside the {}
// is not an expression but a pattern!

<a>blahblah</a> match {
  case <a>{contents}</a> => println("yes! " + contents)
  case _                => println("no! ")
} // yes! blahblah

<a></a> match {
  case <a>{contents}</a> => println("yes! " + contents)
  case _                => println("no! ")
} // no!


<a></a> match {
  case <a>{contents @ _*}</a>   => println("yes! " + contents)
  case _                        => println("no! ")
} // yes! WrappedArray()

val catalog =
  <catalog>
    <cctherm>
      <description>hot dog thermometer</description>
      <yearMade>1952</yearMade>
      <dateObtained>March 14, 2006</dateObtained>
      <bookPrice>2199</bookPrice>
      <purchasePrice>500</purchasePrice>
      <condition>9</condition>
    </cctherm>
    <cctherm>
      <description>Sprite Boy thermometer</description>
      <yearMade>1964</yearMade>
      <dateObtained>April 28, 2003</dateObtained>
      <bookPrice>1695</bookPrice>
      <purchasePrice>595</purchasePrice>
      <condition>5</condition>
    </cctherm>
  </catalog>

/* XML vs Lisp
  (catalog
    (cctherm
      (description "hot dog thermometer")
      (yearMade 1952)
      (dateObtained "March 14, 2006")
      (bookPrice 2199)
      (purchasePrice 500)
      (condition 9))
    (cctherm
      (description "Sprite Boy thermometer")
      (yearMade 1964)
      (dateObtained "April 28, 2003")
      (bookPrice 1695)
      (purchasePrice 595)
      (condition 5)))
*/

// incorrect, we are processing whitespace in between elements
catalog match {
  case <catalog>{therms @ _*}</catalog> =>
    for(therm <- therms)
      println("processing: " +
        (therm \ "description").text)
  }
/*
processing: 
processing: hot dog thermometer
processing: 
processing: Sprite Boy thermometer
processing:
*/

catalog match {
  case <catalog>{therms @ _*}</catalog> =>
    for(therm @ <cctherm>{_*}</cctherm> <- therms)
      println("processing: " +
        (therm \ "description").text)
  }
/*
processing: hot dog thermometer
processing: Sprite Boy thermometer
*/

catalog match {
  case content @ <catalog>{_*}</catalog> => println(content)
}
/*
<catalog>
    <cctherm>
      <description>hot dog thermometer</description>
      <yearMade>1952</yearMade>
      <dateObtained>March 14, 2006</dateObtained>
      <bookPrice>2199</bookPrice>
      <purchasePrice>500</purchasePrice>
      <condition>9</condition>
    </cctherm>
    <cctherm>
      <description>Sprite Boy thermometer</description>
      <yearMade>1964</yearMade>
      <dateObtained>April 28, 2003</dateObtained>
      <bookPrice>1695</bookPrice>
      <purchasePrice>595</purchasePrice>
      <condition>5</condition>
    </cctherm>
  </catalog>
*/




