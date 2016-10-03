import java.math.BigInteger;
import org.spongycastle.math.ec.ECFieldElement;
import org.spongycastle.math.ec.custom.sec.SecP256K1FieldElement;


public class Test_SecP256K1FieldElement extends Test_ECFieldElement {

  @Override
  public void run(){
    logMessage("SecP256K1FieldElement unit test running ...");
    checkSecP256K1FieldElement();
    checkSecP256K1FieldElementFromBigInteger();
    checkAdd();
    checkAddOne();
    checkDivide();
    checkSecP256K1FieldElementEquals();
    checkGetFieldName();
    checkGetFieldSize();
    checkHashCode();
    checkInvert();
    checkIsOne();
    checkIsZero();
    checkMultiply();
    checkNegate();
    checkSqrt();
    checkSquare();
    checkSubtract();
    checkTestBitZero();
    checkToBigInteger();
 
  }

  public void checkSecP256K1FieldElement()
  {
    ECFieldElement x = new SecP256K1FieldElement();
    checkCondition(x.isZero(), "checkSecP256K1FieldElement.1");
  }

  public void checkSecP256K1FieldElementFromBigInteger(){
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = new SecP256K1FieldElement(x.toBigInteger());
    checkEquals(x, y, "checkSecP256K1FieldElementFromBigInteger.1");
    ECFieldElement z = _curve.fromBigInteger(x.toBigInteger());
    checkEquals(x, z, "checkSecP256K1FieldElementFromBigInteger.2");
  }

  public void checkAdd()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = _getRandomElement();
    ECFieldElement z = x.add(y);
    BigInteger xx = x.toBigInteger(); 
    BigInteger yy = y.toBigInteger(); 
    BigInteger zz = xx.add(yy).mod(p); 
    checkEquals(zz, z.toBigInteger(), "checkAdd.1");
  }

  public void checkAddOne()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = x.addOne();
    BigInteger xx = x.toBigInteger();
    BigInteger yy = xx.add(BigInteger.ONE).mod(p);
    checkEquals(yy, y.toBigInteger(), "checkAddOne.1");
  }

  public void checkDivide()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = _getRandomElement();
    ECFieldElement z = x.divide(y);
    BigInteger xx = x.toBigInteger(); 
    BigInteger yy = y.toBigInteger(); 
    BigInteger zz = xx.multiply(yy.modInverse(p)).mod(p);
    checkEquals(zz, z.toBigInteger(), "checkDivide.1");
  }

  public void checkSecP256K1FieldElementEquals()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = _getRandomElement();
    ECFieldElement z = _curve.fromBigInteger(x.toBigInteger());

    checkCondition(x.equals(x), "checkSecP256K1FieldElementEquals.1");
    checkCondition(x.equals(z), "checkSecP256K1FieldElementEquals.2");
    checkCondition(!x.equals(y), "checkSecP256K1FieldElementEquals.3");
    checkEquals(x, x, "checkSecP256K1FieldElementEquals.4");
    checkEquals(x, z, "checkSecP256K1FieldElementEquals.5");
  }

  public void checkGetFieldName()
  {
    ECFieldElement x = _getRandomElement();
    String name = x.getFieldName();
    checkEquals(name, "SecP256K1Field", "checkGetFieldName.1");
  }

  public void checkGetFieldSize(){
    ECFieldElement x = _getRandomElement();
    int size = x.getFieldSize();
    checkEquals(size, 256, "checkGetFieldSize.1");
  }

  public void checkHashCode()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = _getRandomElement();
    ECFieldElement z = _curve.fromBigInteger(x.toBigInteger());
    int hx = x.hashCode();
    int hy = y.hashCode();
    int hz = z.hashCode();

    checkEquals(hx, hz, "checkHashCode.1");
    checkCondition(hx != hy, "checkHashCode.2");
  }

  public void checkInvert()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = x.invert();
    BigInteger xx = x.toBigInteger();
    BigInteger yy = xx.modInverse(p);
    checkEquals(yy, y.toBigInteger(), "checkInverse.1");
  }

  public void checkIsOne()
  {
    ECFieldElement x = _getRandomElement();
    checkCondition(!x.isOne(), "checkIsOne.1");
    ECFieldElement y = _curve.fromBigInteger(BigInteger.ONE);
    checkCondition(y.isOne(), "checkIsOne.2");
  }

  public void checkIsZero()
  {
    ECFieldElement x = _getRandomElement();
    checkCondition(!x.isZero(), "checkIsZero.1");
    ECFieldElement y = _curve.fromBigInteger(BigInteger.ZERO);
    checkCondition(y.isZero(), "checkIsZero.2");
   }

  public void checkMultiply()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = _getRandomElement();
    ECFieldElement z = x.multiply(y);
    BigInteger xx = x.toBigInteger(); 
    BigInteger yy = y.toBigInteger(); 
    BigInteger zz = xx.multiply(yy).mod(p);
    checkEquals(zz, z.toBigInteger(), "checkMultiply.1");
  }

  public void checkNegate()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = x.negate();
    checkCondition(x.add(y).isZero(), "checkNegate.1");
  }

  public void checkSqrt()
  {
    for(int i = 0; i < 20; ++i)
    {
      ECFieldElement x = _getRandomElement();
      ECFieldElement y = x.sqrt();
      if(y != null)
      {
        checkEquals(y.square(), x, "checkSqrt.1");
      }
    }
  }

  public void checkSquare()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = x.square();
    BigInteger xx = x.toBigInteger();
    BigInteger yy = xx.multiply(xx).mod(p);
    checkEquals(yy, y.toBigInteger(), "checkSquare.1");
  }

  public void checkSubtract()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = _getRandomElement();
    ECFieldElement z = x.subtract(y);
    BigInteger xx = x.toBigInteger(); 
    BigInteger yy = y.toBigInteger(); 
    BigInteger zz = xx.subtract(yy).mod(p);
    checkEquals(zz, z.toBigInteger(), "checkSubtract.1"); 
  }

  public void checkTestBitZero()
  {
    for(int i = 0; i < 10; ++i)
    {
      ECFieldElement x = _getRandomElement();
      BigInteger xx = x.toBigInteger();
      checkEquals(x.testBitZero(), xx.testBit(0), "checkTestBitZero.1");
    }
  }

  public void checkToBigInteger()
  {
    ECFieldElement x = _getRandomElement();
    ECFieldElement y = _curve.fromBigInteger(x.toBigInteger());
    checkEquals(x, y, "checkToBigInteger.1");
  }

}
