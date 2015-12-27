object Test{
  def main(args: Array[String]){
    val c = new Complex(1.2, 3.4)
    println("imaginary part: " + c.im())
    val d = new Complex2(1.2,3.4)
    println("imaginary part: " + c.im)
  }
}

class Complex(real: Double, imaginary: Double){
  def re() = real
  def im() = imaginary
}

class Complex2(real: Double, imaginary: Double){
  def re = real
  def im = imaginary
}
