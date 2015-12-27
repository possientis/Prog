object Complex{
  def main(args: Array[String]){
    val c = new Complex2(1.2, 3.4)
    println("imaginary part: " + c.im())
    val d = new Complex(1.2,3.4)
    println("imaginary part: " + c.im)
    println(d)
  }
}

class Complex2(real: Double, imaginary: Double){
  def re() = real
  def im() = imaginary
}

class Complex(real: Double, imaginary: Double){
  def re = real
  def im = imaginary
  override def toString() = 
    "" + re + (if (im < 0) "" else "+") + im + "i"
}
