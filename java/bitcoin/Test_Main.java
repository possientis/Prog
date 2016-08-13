public class Test_Main {
  public static void main(String[] args){

    Test_Interface test; 

    test = new Test_ECKey(); test.run();  // TODO
    test = new Test_VersionedChecksummedBytes(); test.run();
    test = new Test_DumpedPrivateKey(); test.run(); // TODO
    test = new Test_Base58(); test.run(); // TODO
    test = new Test_Sha256Hash(); test.run(); // TODO
  }
}

