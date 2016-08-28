import java.util.Arrays;
import java.security.SecureRandom;

import org.bitcoinj.core.Address;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.WrongNetworkException;

import org.bitcoinj.params.MainNetParams;
import org.bitcoinj.params.TestNet2Params;
import org.bitcoinj.params.RegTestParams; // derives from TestNet2Params
import org.bitcoinj.params.TestNet3Params;
import org.bitcoinj.params.UnitTestParams;


public class Test_Address extends Test_Abstract {
  public void run(){
    logMessage("Address unit test running ...");
    checkLength();
    checkAddress();
    checkClone();
    checkFromBase58();
    checkFromP2SHHash();
    checkFromP2SHScript();
    checkGetHash160();
    checkGetParameters();
    checkGetParametersFromAddress();
    checkIsP2SHAddress();
  }

  private static final NetworkParameters _params1 = MainNetParams.get();
  private static final NetworkParameters _params2 = TestNet2Params.get();
  private static final NetworkParameters _params3 = RegTestParams.get();
  private static final NetworkParameters _params4 = TestNet3Params.get();
  private static final NetworkParameters _params5 = UnitTestParams.get();

  private static final int _version1 = _params1.getAddressHeader();
  private static final int _version2 = _params2.getAddressHeader();
  private static final int _version3 = _params3.getAddressHeader();
  private static final int _version4 = _params4.getAddressHeader();
  private static final int _version5 = _params5.getAddressHeader();

  private static final int _P2SHversion1 = _params1.getP2SHHeader();
  private static final int _P2SHversion2 = _params2.getP2SHHeader();
  private static final int _P2SHversion3 = _params3.getP2SHHeader();
  private static final int _P2SHversion4 = _params4.getP2SHHeader();
  private static final int _P2SHversion5 = _params5.getP2SHHeader();

  // returns array of random pay to public key hash addresses
  // which correspond to the same hash and each possible network
  private static Address[] _getRandomAddress(){
    Address[] addresses = new Address[6]; // index 0 not used
    byte[] hash = getRandomBytes(20);
    addresses[0] = null;
    addresses[1] = new Address(_params1, _version1, hash);  // MainNetParams
    addresses[2] = new Address(_params2, _version2, hash);  // TestNet2Params
    addresses[3] = new Address(_params3, _version3, hash);  // RegTestParams
    addresses[4] = new Address(_params4, _version4, hash);  // TestNet3Params
    addresses[5] = new Address(_params5, _version5, hash);  // UnitTestParams

    return addresses;
  }
 
  // returns array of random pay to script hash addresses
  // which correspond to the same hash and each possible network
  private static Address[] _getRandomP2SHAddress(){
    Address[] addresses = new Address[6]; // index 0 not used
    byte[] hash = getRandomBytes(20);
    addresses[0] = null;
    addresses[1] = new Address(_params1, _P2SHversion1, hash);  // MainNetParams
    addresses[2] = new Address(_params2, _P2SHversion2, hash);  // TestNet2Params
    addresses[3] = new Address(_params3, _P2SHversion3, hash);  // RegTestParams
    addresses[4] = new Address(_params4, _P2SHversion4, hash);  // TestNet3Params
    addresses[5] = new Address(_params5, _P2SHversion5, hash);  // UnitTestParams

    return addresses;
  }
 
  public void checkLength(){
    checkEquals(Address.LENGTH, 20, "checkLength.1");
  }

  public void checkAddress(){
    byte[] hash = getRandomBytes(20);

    // normal (pay to public key hash) addresses
    Address address1 = new Address(_params1, hash);
    Address address2 = new Address(_params2, hash);
    Address address3 = new Address(_params3, hash);
    Address address4 = new Address(_params4, hash);
    Address address5 = new Address(_params5, hash);

    checkCondition(Arrays.equals(hash, address1.getHash160()), "checkAddress.1");
    checkCondition(Arrays.equals(hash, address2.getHash160()), "checkAddress.2");
    checkCondition(Arrays.equals(hash, address3.getHash160()), "checkAddress.3");
    checkCondition(Arrays.equals(hash, address4.getHash160()), "checkAddress.4");
    checkCondition(Arrays.equals(hash, address5.getHash160()), "checkAddress.5");

    checkEquals(_params1, address1.getParameters(), "checkAddress.6");
    checkEquals(_params2, address2.getParameters(), "checkAddress.7");
    checkEquals(_params3, address3.getParameters(), "checkAddress.8");
    checkEquals(_params4, address4.getParameters(), "checkAddress.9");
    checkEquals(_params5, address5.getParameters(), "checkAddress.10");

    int version1 = _params1.getAddressHeader();
    int version2 = _params2.getAddressHeader();
    int version3 = _params3.getAddressHeader();
    int version4 = _params4.getAddressHeader();
    int version5 = _params5.getAddressHeader();

    Address check1 = new Address(_params1, version1, hash);
    Address check2 = new Address(_params2, version2, hash);
    Address check3 = new Address(_params3, version3, hash);
    Address check4 = new Address(_params4, version4, hash);
    Address check5 = new Address(_params5, version5, hash);

    checkEquals(check1, address1, "checkAddress.11");
    checkEquals(check2, address2, "checkAddress.12");
    checkEquals(check3, address3, "checkAddress.13");
    checkEquals(check4, address4, "checkAddress.14");
    checkEquals(check5, address5, "checkAddress.15");

    int p2sh1 = _params1.getP2SHHeader();
    int p2sh2 = _params2.getP2SHHeader();
    int p2sh3 = _params3.getP2SHHeader();
    int p2sh4 = _params4.getP2SHHeader();
    int p2sh5 = _params5.getP2SHHeader();

    // pay to script hash addresses
    Address p2shAdd1 = new Address(_params1, p2sh1, hash);
    Address p2shAdd2 = new Address(_params2, p2sh2, hash);
    Address p2shAdd3 = new Address(_params3, p2sh3, hash);
    Address p2shAdd4 = new Address(_params4, p2sh4, hash);
    Address p2shAdd5 = new Address(_params5, p2sh5, hash);

    // same hash but different version number, addresses should be different
    checkCondition(!address1.equals(p2shAdd1), "checkAddress.16");
    checkCondition(!address2.equals(p2shAdd1), "checkAddress.17");
    checkCondition(!address3.equals(p2shAdd1), "checkAddress.18");
    checkCondition(!address4.equals(p2shAdd1), "checkAddress.19");
    checkCondition(!address5.equals(p2shAdd1), "checkAddress.20");

    // attempting to build address from an incompatible version should fail
    Address check;

    // MainNetParams
    try{
      check = new Address(_params1, 111, hash); // 111 test pay to public key hash
      checkCondition(false, "checkAddress.21"); 
    } catch (WrongNetworkException e) {}
    // main network with test (pay to script hash) address
    try{
      check = new Address(_params1, 196, hash); // 196 test pay to script hash
      checkCondition(false, "checkAddress.22"); 
    } catch (WrongNetworkException e) {}

    // Test2NetParams
    try{
      check = new Address(_params2, 0, hash); // 0 main pay to public key hash
      checkCondition(false, "checkAddress.23"); 
    } catch (WrongNetworkException e) {}
    // main network with test (pay to script hash) address
    try{
      check = new Address(_params2, 5, hash); // 5 main pay to script hash
      checkCondition(false, "checkAddress.24"); 
    } catch (WrongNetworkException e) {}

    // RegTestParams
    try{
      check = new Address(_params3, 0, hash); // 0 main pay to public key hash
      checkCondition(false, "checkAddress.25"); 
    } catch (WrongNetworkException e) {}
    // main network with test (pay to script hash) address
    try{
      check = new Address(_params3, 5, hash); // 5 main pay to script hash
      checkCondition(false, "checkAddress.26"); 
    } catch (WrongNetworkException e) {}

    // TestNet3Params
    try{
      check = new Address(_params4, 0, hash); // 0 main pay to public key hash
      checkCondition(false, "checkAddress.27"); 
    } catch (WrongNetworkException e) {}
    // main network with test (pay to script hash) address
    try{
      check = new Address(_params4, 5, hash); // 5 main pay to script hash
      checkCondition(false, "checkAddress.28"); 
    } catch (WrongNetworkException e) {}

    // UnitTestParams
    try{
      check = new Address(_params5, 0, hash); // 0 main pay to public key hash
      checkCondition(false, "checkAddress.29"); 
    } catch (WrongNetworkException e) {}
    // main network with test (pay to script hash) address
    try{
      check = new Address(_params5, 5, hash); // 5 main pay to script hash
      checkCondition(false, "checkAddress.30"); 
    } catch (WrongNetworkException e) {}

  }

  public void checkClone(){
    Address check;

    // pay to public key hash address
    Address[] P2PKH = _getRandomAddress();
    for(int i = 1; i <= 5; ++i){
      try{
        check = P2PKH[i].clone();
        checkEquals(check, P2PKH[i], "checkClone.1");
      } catch (Exception e) {
        checkCondition(false, "checkClone.2");
      }
    }

    // pay to script hash address
    Address[] P2SH = _getRandomP2SHAddress();
    for(int i = 1; i <= 5; ++i){
      try{
        check = P2SH[i].clone();
        checkEquals(check, P2SH[i], "checkClone.3");
      } catch (Exception e) {
        checkCondition(false, "checkClone.3");
      }
    }

    // clone does not perform deep copy
    logMessage("-> Address::clone see unit test code ...");
    Address address1 = P2PKH[1];
    Address address2 = null;
    try {address2 = address1.clone(); } catch(Exception e){}
    byte[] hash = address1.getHash160();  // internal exposed
    for(int i = 0; i < 20; ++i){
      hash[i] = (byte) 0x00;  // both address1 & address2 corrupted
    }
  }

  public void checkFromBase58(){
    Address check;

    // pay-to-public-key-hash addresses
    Address[] P2PKH = _getRandomAddress();

    // MainNetParams
    check = Address.fromBase58(_params1, P2PKH[1].toString());
    checkEquals(check, P2PKH[1], "checkFromBase58.1");

    // TestNet2Params
    check = Address.fromBase58(_params2, P2PKH[2].toString());
    checkEquals(check, P2PKH[2], "checkFromBase58.2");
    
    // RegTestParams
    check = Address.fromBase58(_params3, P2PKH[3].toString());
    checkEquals(check, P2PKH[3], "checkFromBase58.3");

    // TestNet3Params
    check = Address.fromBase58(_params4, P2PKH[4].toString());
    checkEquals(check, P2PKH[4], "checkFromBase58.4");

    // TestNet2Params
    check = Address.fromBase58(_params2, P2PKH[5].toString());
    checkEquals(check, P2PKH[5], "checkFromBase58.5");

    // pay-to-script-hash addresses
    Address[] P2SH = _getRandomP2SHAddress();

    // MainNetParams
    check = Address.fromBase58(_params1, P2SH[1].toString());
    checkEquals(check, P2SH[1], "checkFromBase58.1");

    // TestNet2Params
    check = Address.fromBase58(_params2, P2SH[2].toString());
    checkEquals(check, P2SH[2], "checkFromBase58.2");
    
    // RegTestParams
    check = Address.fromBase58(_params3, P2SH[3].toString());
    checkEquals(check, P2SH[3], "checkFromBase58.3");

    // TestNet3Params
    check = Address.fromBase58(_params4, P2SH[4].toString());
    checkEquals(check, P2SH[4], "checkFromBase58.4");

    // TestNet2Params
    check = Address.fromBase58(_params2, P2SH[5].toString());
    checkEquals(check, P2SH[5], "checkFromBase58.5");

    // the network parameter is redundant as it is encoded in
    // the address. We expect an exception to be thrown an 
    // inconsistency is thrown.
    
    // MainNetParams
    try{
      check = Address.fromBase58(_params1, P2PKH[2].toString());
      checkCondition(false, "checkFromBase58.6"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params1, P2PKH[3].toString());
      checkCondition(false, "checkFromBase58.7"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params1, P2PKH[4].toString());
      checkCondition(false, "checkFromBase58.8"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params1, P2PKH[5].toString());
      checkCondition(false, "checkFromBase58.9"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params1, P2SH[2].toString());
      checkCondition(false, "checkFromBase58.10"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params1, P2SH[3].toString());
      checkCondition(false, "checkFromBase58.11"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params1, P2SH[4].toString());
      checkCondition(false, "checkFromBase58.12"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params1, P2SH[5].toString());
      checkCondition(false, "checkFromBase58.13"); // no exception thrown
    } catch(WrongNetworkException e){}

    // TestNet2Params    
    try{
      check = Address.fromBase58(_params2, P2PKH[1].toString());
      checkCondition(false, "checkFromBase58.14"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params2, P2SH[1].toString());
      checkCondition(false, "checkFromBase58.15"); // no exception thrown
    } catch(WrongNetworkException e){}
  
    // RegTestParams    
    try{
      check = Address.fromBase58(_params3, P2PKH[1].toString());
      checkCondition(false, "checkFromBase58.16"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params3, P2SH[1].toString());
      checkCondition(false, "checkFromBase58.17"); // no exception thrown
    } catch(WrongNetworkException e){}
 
    // TestNet3Params    
    try{
      check = Address.fromBase58(_params4, P2PKH[1].toString());
      checkCondition(false, "checkFromBase58.16"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params4, P2SH[1].toString());
      checkCondition(false, "checkFromBase58.17"); // no exception thrown
    } catch(WrongNetworkException e){}

    // UnitTestParams
    try{
      check = Address.fromBase58(_params5, P2PKH[1].toString());
      checkCondition(false, "checkFromBase58.16"); // no exception thrown
    } catch(WrongNetworkException e){}
    try{
      check = Address.fromBase58(_params5, P2SH[1].toString());
      checkCondition(false, "checkFromBase58.17"); // no exception thrown
    } catch(WrongNetworkException e){}
  }

  public void checkFromP2SHHash(){
    byte[] hash;
    Address check;
    Address[] P2SH = _getRandomP2SHAddress();
    
    // MainNetParams
    hash = P2SH[1].getHash160();
    check = Address.fromP2SHHash(_params1, hash);
    checkEquals(check, P2SH[1], "checkFromP2SHHash.1");
    // TestNet2Params
    hash = P2SH[2].getHash160();
    check = Address.fromP2SHHash(_params2, hash);
    checkEquals(check, P2SH[2], "checkFromP2SHHash.2");
     // RegTestParams
    hash = P2SH[3].getHash160();
    check = Address.fromP2SHHash(_params3, hash);
    checkEquals(check, P2SH[3], "checkFromP2SHHash.3");
      // TestNet3Params
    hash = P2SH[4].getHash160();
    check = Address.fromP2SHHash(_params4, hash);
    checkEquals(check, P2SH[4], "checkFromP2SHHash.4");
     // UnitTestParams
    hash = P2SH[5].getHash160();
    check = Address.fromP2SHHash(_params5, hash);
    checkEquals(check, P2SH[5], "checkFromP2SHHash.5");
  }

  public void checkFromP2SHScript(){/* TODO */}

  public void checkGetHash160(){
    byte [] hash = getRandomBytes(20);
    Address address;
    byte[] check;

    // MainNetParams
    address = new Address(_params1, _version1, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.1a");

    address = new Address(_params1, _P2SHversion1, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.1b");

    // TestNet2Params
    address = new Address(_params2, _version2, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.2a");

    address = new Address(_params2, _P2SHversion2, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.2b");

    // RegTestParams
    address = new Address(_params3, _version3, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.3a");

    address = new Address(_params3, _P2SHversion3, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.3b");

    // TestNet3Params
    address = new Address(_params4, _version4, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.4a");

    address = new Address(_params4, _P2SHversion4, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.4b");

    // UnitTestParams
    address = new Address(_params5, _version5, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.5a");

    address = new Address(_params5, _P2SHversion5, hash);
    check = address.getHash160();
    checkCondition(Arrays.equals(check, hash), "checkGetHash160.5b");
  }

  public void checkGetParameters(){

    Address[] addresses = _getRandomAddress();

    checkEquals(_params1, addresses[1].getParameters(), "checkGetParameters.1");
    checkEquals(_params2, addresses[2].getParameters(), "checkGetParameters.2");
    checkEquals(_params3, addresses[3].getParameters(), "checkGetParameters.3");
    checkEquals(_params4, addresses[4].getParameters(), "checkGetParameters.4");
    checkEquals(_params5, addresses[5].getParameters(), "checkGetParameters.5");

    addresses = _getRandomP2SHAddress();

    checkEquals(_params1, addresses[1].getParameters(), "checkGetParameters.1");
    checkEquals(_params2, addresses[2].getParameters(), "checkGetParameters.2");
    checkEquals(_params3, addresses[3].getParameters(), "checkGetParameters.3");
    checkEquals(_params4, addresses[4].getParameters(), "checkGetParameters.4");
    checkEquals(_params5, addresses[5].getParameters(), "checkGetParameters.5");
  }


  public void checkGetParametersFromAddress(){

    logMessage("-> Address::getParametersFromAddress see unit test code ...");

    // the version byte of an address is the same on the 4 test networks
    // Hence there is no way this function can know which underlying 
    // network an address was produced from. If the version byte corresponds
    // to a test network, then the class TestNet3Params is the selected
    // class. 

    NetworkParameters check;
    Address[] addresses = _getRandomAddress();

    check = Address.getParametersFromAddress(addresses[1].toString());
    checkEquals(check, _params1, "checkGetParametersFromAddress.1");
    
    check = Address.getParametersFromAddress(addresses[2].toString());
//  checkEquals(check, _params2, "checkGetParametersFromAddress.2");
    
    check = Address.getParametersFromAddress(addresses[3].toString());
//  checkEquals(check, _params3, "checkGetParametersFromAddress.3");

    check = Address.getParametersFromAddress(addresses[4].toString());
    checkEquals(check, _params4, "checkGetParametersFromAddress.4");

    check = Address.getParametersFromAddress(addresses[5].toString());
//  checkEquals(check, _params5, "checkGetParametersFromAddress.5");

    addresses = _getRandomP2SHAddress();

    check = Address.getParametersFromAddress(addresses[1].toString());
    checkEquals(check, _params1, "checkGetParametersFromAddress.1");

    check = Address.getParametersFromAddress(addresses[4].toString());
    checkEquals(check, _params4, "checkGetParametersFromAddress.4");
  }

  public void checkIsP2SHAddress(){
    Address[] P2PKH = _getRandomAddress();
    Address[] P2SH = _getRandomP2SHAddress();

    for(int i = 1; i <= 5; ++i){
      checkEquals(false, P2PKH[i].isP2SHAddress(), "checkIsP2SHAddress.1");
      checkEquals(true, P2SH[i].isP2SHAddress(), "checkIsP2SHAddress.2");
    }
  }

}





