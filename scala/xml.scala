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
      <condition>condition</condition>
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
      <condition>condition</condition>
    </cctherm>
*/

// you escape '{' and '}' within xml text with {{ and }}.
val x2 = <a> }}}} brace yourself! {{{{ </a>
println(x2) // <a> }} brace yourself! {{ </a>




