//type Color.Value                  // enum
object Color extends Enumeration {  // enum
  val red, green, blue = Value      // enum 
}


val x:Color.Value = Color.red
