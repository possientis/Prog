class Rational(n: Int, d: Int) {
  private def gcd(a: Int, b: Int): Int =
    if (b == 0) a else gcd(b, a % b)
  private val g = gcd(n, d)
  val numer: Int = n / g
  val denom: Int = d / g
  println("created: "+numer+"/"+denom)
  def this(n: Int) = this(n,1)
  def add(that: Rational): Rational =
    new Rational(numer * that.denom + that.numer * denom, denom * that.denom)
  def sub(that: Rational): Rational =
    new Rational(numer * that.denom - that.numer * denom, denom * that.denom)
  def mul(that: Rational): Rational =
    new Rational(numer * that.numer, denom * that.denom)
  def div(that: Rational): Rational =
  new Rational(numer * that.denom, denom * that.numer)
  override def toString() = numer+"/"+denom
}


val x = new Rational(6,0)
println("x = "+x)
