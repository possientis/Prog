import java.util.Arrays;
import java.math.BigInteger;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

import com.google.common.base.Objects;

import org.spongycastle.asn1.DERSequenceGenerator;
import org.spongycastle.asn1.ASN1Integer;

import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.Sha256Hash;

public class Test_ECDSASignature extends Test_ECKey 
{

  @Override
  public void run()
  {
    logMessage("ECKey.ECDSASignature unit test running ...");
    checkFieldR();
    checkFieldS();
    checkECDSASignature();
    checkDecodeFromDER();
    checkEncodeToDER();
    checkSigEquals();
    checkHashCode();
    checkIsCanonical();
    checkToCanonicalised();
  }

  private byte[] _encodeDER(ECKey.ECDSASignature sig)
  {
    // Usually 70-72 bytes
    ByteArrayOutputStream baos = new ByteArrayOutputStream(72);
    DERSequenceGenerator seq = null;

    try
    {
      seq = new DERSequenceGenerator(baos);
    }
    catch(IOException e)
    {
      checkCondition(false, "_EncodeDER.1");
    }

    try
    {
      seq.addObject(new ASN1Integer(sig.r));
    }
    catch(IOException e)
    {
      checkCondition(false, "_EncodeDER.2");
    }

    try
    {
      seq.addObject(new ASN1Integer(sig.s));
    }
    catch(IOException e)
    {
      checkCondition(false, "_EncodeDER.3");
    }

    try
    {
      seq.close();
    }
    catch(IOException e)
    {
      checkCondition(false, "_EncodeDER.4");
    }

    return baos.toByteArray();

  }

  public void checkFieldR()
  {

    byte[] r = getRandomBytes(32);
    byte[] s = getRandomBytes(32);

    BigInteger rN = new BigInteger(1, r);
    BigInteger sN = new BigInteger(1, s);

    ECKey.ECDSASignature sig = new ECKey.ECDSASignature(rN,sN);

    checkEquals(rN, sig.r, "checkFieldR.1");

  }

  public void checkFieldS()
  {

    byte[] r = getRandomBytes(32);
    byte[] s = getRandomBytes(32);

    BigInteger rN = new BigInteger(1, r);
    BigInteger sN = new BigInteger(1, s);

    ECKey.ECDSASignature sig = new ECKey.ECDSASignature(rN,sN);

    checkEquals(sN, sig.s, "checkFieldS.1");

  }

  public void checkECDSASignature()
  {

    byte[] r = getRandomBytes(32);
    byte[] s = getRandomBytes(32);

    BigInteger rN = new BigInteger(1, r);
    BigInteger sN = new BigInteger(1, s);

    ECKey.ECDSASignature sig = new ECKey.ECDSASignature(rN,sN);
    checkNotNull(sig, "checkECDSASignature.1");
  }


  public void checkDecodeFromDER()
  {
    ECKey key = new ECKey();
    Sha256Hash hash = Sha256Hash.wrap(getRandomBytes(32));
    ECKey.ECDSASignature sig1 = key.sign(hash);

    byte[] der = sig1.encodeToDER();

    ECKey.ECDSASignature sig2 = ECKey.ECDSASignature.decodeFromDER(der);
    checkEquals(sig1, sig2, "checkDecodeFromDER.1");
  }

  public void checkEncodeToDER()
  {
    ECKey key = new ECKey();
    Sha256Hash hash = Sha256Hash.wrap(getRandomBytes(32));
    ECKey.ECDSASignature sig = key.sign(hash);

    byte[] check = _encodeDER(sig);
    byte[] der = sig.encodeToDER();

    checkCondition(Arrays.equals(check, der), "checkEncodeDER.1");
  }

  public void checkSigEquals()
  {
    BigInteger r1 = new BigInteger(1, getRandomBytes(32));
    BigInteger r2 = new BigInteger(1, getRandomBytes(32));
    BigInteger s1 = new BigInteger(1, getRandomBytes(32));
    BigInteger s2 = new BigInteger(1, getRandomBytes(32));

    ECKey.ECDSASignature sig11 = new ECKey.ECDSASignature(r1, s1);
    ECKey.ECDSASignature sig21 = new ECKey.ECDSASignature(r2, s1);
    ECKey.ECDSASignature sig12 = new ECKey.ECDSASignature(r1, s2);
    ECKey.ECDSASignature sig22 = new ECKey.ECDSASignature(r2, s2);

    checkCondition(sig11.equals(sig11), "checkSigEquals.1");
    checkCondition(sig12.equals(sig12), "checkSigEquals.2");
    checkCondition(sig21.equals(sig21), "checkSigEquals.3");
    checkCondition(sig22.equals(sig22), "checkSigEquals.4");


    checkCondition(!sig11.equals(sig12), "checkSigEquals.5");
    checkCondition(!sig11.equals(sig21), "checkSigEquals.6");
    checkCondition(!sig11.equals(sig22), "checkSigEquals.7");

  }

  public void checkHashCode()
  {
    ECKey key = new ECKey();
    Sha256Hash hash = Sha256Hash.wrap(getRandomBytes(32));
    ECKey.ECDSASignature sig = key.sign(hash);
    int check = Objects.hashCode(sig.r, sig.s);
    checkEquals(check, sig.hashCode(), "checkHashCode.1");
  }

  public void checkIsCanonical()
  {
    BigInteger order = ECKey.CURVE.getN();
    ECKey key = new ECKey();
    Sha256Hash hash = Sha256Hash.wrap(getRandomBytes(32));
    ECKey.ECDSASignature sig1 = key.sign(hash);
    BigInteger t = sig1.s.negate().mod(order); 
    ECKey.ECDSASignature sig2 = new ECKey.ECDSASignature(sig1.r, t); // (r, -s)

    if(sig1.s.compareTo(ECKey.HALF_CURVE_ORDER) <= 0)
    {
      checkCondition(sig1.isCanonical(), "checkIsCanonical.1");
      checkCondition(!sig2.isCanonical(), "checkIsCanonical.2");
    }
    else
    {
      checkCondition(!sig1.isCanonical(), "checkIsCanonical.3");
      checkCondition(sig2.isCanonical(), "checkIsCanonical.4");
    } 
  }


  public void checkToCanonicalised()
  {
    BigInteger order = ECKey.CURVE.getN();
    ECKey key = new ECKey();
    Sha256Hash hash = Sha256Hash.wrap(getRandomBytes(32));
    ECKey.ECDSASignature sig1 = key.sign(hash);
    BigInteger t = sig1.s.negate().mod(order); 
    ECKey.ECDSASignature sig2 = new ECKey.ECDSASignature(sig1.r, t); // (r, -s)

    if(sig1.s.compareTo(ECKey.HALF_CURVE_ORDER) <= 0)
    {
      checkEquals(sig1, sig1.toCanonicalised(), "checkToCanonicalised.1");
      checkEquals(sig1, sig2.toCanonicalised(), "checkToCanonicalised.2");
    }
    else
    {
      checkEquals(sig2, sig1.toCanonicalised(), "checkToCanonicalised.3");
      checkEquals(sig2, sig2.toCanonicalised(), "checkToCanonicalised.4");
    }
  }

}
