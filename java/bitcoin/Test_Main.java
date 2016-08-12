public class Test_Main {
  public static void main(String[] args){

    Test_Interface test; 

    test = new Test_ECKey(); test.run();
    test = new Test_VersionedChecksummedBytes(); test.run();


  }
}

