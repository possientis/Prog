public class Test_Main {
  public static void main(String[] args){

    Test_Abstract test; 

    test = new Test_ECKey(); test.run();
    test = new Test_ECKey_ECDSASignature(); test.run();             
    test = new Test_VersionedChecksummedBytes(); test.run();
    test = new Test_DumpedPrivateKey(); test.run();
    test = new Test_Base58(); test.run();
    test = new Test_Sha256Hash(); test.run();
    test = new Test_LazyECPoint(); test.run();                // TODO
    test = new Test_ECPoint(); test.run();       
    test = new Test_ECPoint_AbstractFp(); test.run();
    test = new Test_SecP256K1Point(); test.run();
    test = new Test_ECFieldElement(); test.run();
    test = new Test_SecP256K1FieldElement(); test.run();  
    test = new Test_Address(); test.run();
    test = new Test_NetworkParameters(); test.run();          
    test = new Test_AbstractBitcoinNetParams(); test.run();   
    test = new Test_MainNetParams(); test.run();              
    test = new Test_TestNet2Params(); test.run();             
    test = new Test_RegTestParams(); test.run();              
    test = new Test_TestNet3Params(); test.run();             
    test = new Test_UnitTestParams(); test.run();             
    test = new Test_Base64Encoder(); test.run();
    test = new Test_Base64(); test.run();
  }
}

