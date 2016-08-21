import org.bitcoinj.core.Address;

public class Test_Address implements Test_Interface {
  public void run(){
    logMessage("Address unit test running ...");
    checkLength();
    checkAddress();
    checkAddressFromVersion();
    checkClone();
    checkFromBase58();
    checkFromP2SHHash();
    checkFromP2SHScript();
    checkGetHash160();
    checkGetParameters();
    checkGetParametersFromAddress();
    checkIsP2SHAddress();
  }


  public void checkLength(){
    checkEquals(Address.LENGTH, 20, "checkLength.1");
  }

  public void checkAddress(){/* TODO */}
  public void checkAddressFromVersion(){/* TODO */}
  public void checkClone(){/* TODO */}
  public void checkFromBase58(){/* TODO */}
  public void checkFromP2SHHash(){/* TODO */}
  public void checkFromP2SHScript(){/* TODO */}
  public void checkGetHash160(){/* TODO */}
  public void checkGetParameters(){/* TODO */}
  public void checkGetParametersFromAddress(){/* TODO */}
  public void checkIsP2SHAddress(){/* TODO */}



}





