public class Test_Main {
  public static void main(String[] args){

    Test_Interface test; 

    test = new Test_ECKey(); test.run();              // TODO
    test = new Test_VersionedChecksummedBytes(); test.run();
    test = new Test_DumpedPrivateKey(); test.run();
    test = new Test_Base58(); test.run();
    test = new Test_Sha256Hash(); test.run();
    test = new Test_LazyECPoint(); test.run();        // TODO
    test = new Test_ECPoint(); test.run();            // TODO
    test = new Test_ECFieldElement(); test.run();     // TODO
    test = new Test_Address(); test.run();            // TODO
    test = new Test_NetworkParameters(); test.run();  // TODO
  }
}

