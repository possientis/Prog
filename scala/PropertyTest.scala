// Property idiom in scala
class Foo(private var _name:String){ // need 'var' if creating setter 
  
  def name = _name
  def name_=(name: String) = {_name = name}

}

class Bar {
  private var _name: String = _ // null?
  
  def name = _name
  def name_=(name: String) = _name = name // even {...} optional
}


object PropertyTest {

  def main(args: Array[String]){

    println("This is running")

    val o = new Foo("john")
    println(o.name)
    o.name = "luc"
    println(o.name)


    val p = new Bar()
    println(p.name)
    p.name = "luc"
    println(p.name)

  }
}
