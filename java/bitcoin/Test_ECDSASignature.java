import java.math.BigInteger;

import org.bitcoinj.core.ECKey;

public class Test_ECDSASignature extends Test_ECKey {

  @Override
  public void run(){
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


  public void checkFieldR(){

    byte[] r = getRandomBytes(32);
    byte[] s = getRandomBytes(32);

    BigInteger rN = new BigInteger(1, r);
    BigInteger sN = new BigInteger(1, s);

    ECKey.ECDSASignature sig = new ECKey.ECDSASignature(rN,sN);

    checkEquals(rN, sig.r, "checkFieldR.1");

  }

  public void checkFieldS(){

    byte[] r = getRandomBytes(32);
    byte[] s = getRandomBytes(32);

    BigInteger rN = new BigInteger(1, r);
    BigInteger sN = new BigInteger(1, s);

    ECKey.ECDSASignature sig = new ECKey.ECDSASignature(rN,sN);

    checkEquals(sN, sig.s, "checkFieldS.1");

  }

  public void checkECDSASignature(){

    byte[] r = getRandomBytes(32);
    byte[] s = getRandomBytes(32);

    BigInteger rN = new BigInteger(1, r);
    BigInteger sN = new BigInteger(1, s);

    ECKey.ECDSASignature sig = new ECKey.ECDSASignature(rN,sN);
    checkNotNull(sig, "checkECDSASignature.1");
  }


  public void checkDecodeFromDER(){ /* TODO */ }
  public void checkEncodeToDER(){ /* TODO */ }
  public void checkSigEquals(){ /* TODO */ }
  public void checkHashCode(){ /* TODO */ }
  public void checkIsCanonical(){ /* TODO */ }
  public void checkToCanonicalised(){ /* TODO */ }

}
