import java.math.BigInteger;
import org.spongycastle.math.ec.ECFieldElement;
import org.spongycastle.math.ec.ECCurve;
import org.bitcoinj.core.ECKey;

public class Test_ECFieldElement extends Test_Abstract{

  public void run(){

    logMessage("ECFieldElement unit test running ...");
    checkECFieldElementF2m();
    checkECFieldElementFp();
    checkEIGHT();
    checkFOUR();
    checkONE();
    checkTHREE();
    checkTWO();
    checkZERO();
    checkBitLength();
    checkGetEncoded();
    checkMultiplyMinusProduct();
    checkMultiplyPlusProduct();
    checkSquareMinusProduct();
    checkSquarePlusProduct();
    checkSquarePow();
    checkToString();
  }

  protected static final ECCurve _curve = ECKey.CURVE.getCurve();
  protected static final BigInteger p = _curve.getField().getCharacteristic();
  protected static ECFieldElement _getRandomElement()
  {
    byte[] bytes = getRandomBytes(32);
    BigInteger n = new BigInteger(1, bytes);
    return _curve.fromBigInteger(n.mod(p));
  }

  public void checkECFieldElementF2m()
  {
    ECFieldElement.F2m x = null;  // compile time
  }

  public void checkECFieldElementFp()
  {
    ECFieldElement.Fp x = null; // compile time
  }

  public void checkEIGHT()
  {
    BigInteger x = ECFieldElement.EIGHT;
    BigInteger y = BigInteger.valueOf(8);
    checkEquals(x, y, "checkEIGHT.1");
  }

  public void checkFOUR()
  {
    BigInteger x = ECFieldElement.FOUR;
    BigInteger y = BigInteger.valueOf(4);
    checkEquals(x, y, "checkFOUR.1");
  }

  public void checkONE()
  {
    BigInteger x = ECFieldElement.ONE;
    BigInteger y = BigInteger.ONE;
    checkEquals(x, y, "checkONE.1");
  }

  public void checkTHREE()
  {
    BigInteger x = ECFieldElement.THREE;
    BigInteger y = BigInteger.valueOf(3);
    checkEquals(x, y, "checkTHREE.1");
  }

  public void checkTWO()
  {
    BigInteger x = ECFieldElement.TWO;
    BigInteger y = BigInteger.valueOf(2);
    checkEquals(x, y, "checkTWO.1");
  }

  public void checkZERO()
  {
    BigInteger x = ECFieldElement.ZERO;
    BigInteger y = BigInteger.ZERO;
    checkEquals(x, y, "checkZERO.1");
  }

  public void checkBitLength()
  {
    ECFieldElement x = _getRandomElement();
    int num1 = x.bitLength();
    int num2 = x.toBigInteger().bitLength();
    checkEquals(num1, num2, "checkBitLength.1");
  }

  public void checkGetEncoded()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = x.negate();

    BigInteger nx = x.toBigInteger();
    BigInteger ny = y.toBigInteger();

    byte[] bx = x.getEncoded();
    byte[] by = y.getEncoded();

    BigInteger  mx = new BigInteger(1, bx);
    BigInteger  my = new BigInteger(1, by);

    checkEquals(nx, mx, "checkGetEncoded.1");
    checkEquals(ny, my, "checkGetEncoded.2");
  }

  public void checkMultiplyMinusProduct(){ /* TODO */ }
  public void checkMultiplyPlusProduct(){ /* TODO */ }
  public void checkSquareMinusProduct(){ /* TODO */ }
  public void checkSquarePlusProduct(){ /* TODO */ }
  public void checkSquarePow(){ /* TODO */ }

  public void checkToString()
  {
    ECFieldElement x = _getRandomElement();
    String s1 = x.toString();
    String s2 = x.toBigInteger().toString(16);
    checkEquals(s1, s2, "checkToString.1");
  }

}



































