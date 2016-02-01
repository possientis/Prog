import java.math.BigInteger

object JavaTest {
  def main(args: Array[String]){
    

  }

  def factorial(x: BigInteger): BigInteger =
    if (x == BigInteger.ZERO)
      BigInteger.ONE
    else
      x.multiply(factorial(x.subtract(BigInteger.ONE)))
}
