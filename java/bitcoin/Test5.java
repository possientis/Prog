import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.params.MainNetParams;
import org.bitcoinj.params.TestNet2Params;
import org.bitcoinj.params.RegTestParams;
import org.bitcoinj.params.TestNet3Params;
import org.bitcoinj.params.UnitTestParams;


public class Test5 {

  public static void main(String args[]){

    // bitcoinj has 5 concrete types of NetworkParams
    NetworkParameters net1 = MainNetParams.get();
    NetworkParameters net2 = TestNet2Params.get();
    NetworkParameters net3 = RegTestParams.get(); // derives from TestNet2Params
    NetworkParameters net4 = TestNet3Params.get();
    NetworkParameters net5 = UnitTestParams.get();

    // net2 and net4 have the same Id
    System.out.println(net1.getId()); // org.bitcoin.production
    System.out.println(net2.getId()); // org.bitcoin.test
    System.out.println(net3.getId()); // org.bitcoin.regtest
    System.out.println(net4.getId()); // org.bitcoin.test
    System.out.println(net5.getId()); // org.bitcoinj.unittest (yes, 'bitcoinj')

    // net2 and net4 are not equal: they have different classes
    System.out.println(net2.equals(net4));  // false 

    // however, net2 and net4 have the same hashCode, which ignores the class
    System.out.println(net2.hashCode());  // 348975691
    System.out.println(net4.hashCode());  // 348975691

    // One consequence of non-uniqueness of ID is this:
    NetworkParameters check1 = NetworkParameters.fromID(net1.getId());
    NetworkParameters check2 = NetworkParameters.fromID(net2.getId());
    NetworkParameters check3 = NetworkParameters.fromID(net3.getId());
    NetworkParameters check4 = NetworkParameters.fromID(net4.getId());
    NetworkParameters check5 = NetworkParameters.fromID(net5.getId());

    System.out.println(net1.equals(check1));  // true 
    System.out.println(net2.equals(check2));  // false
    System.out.println(net3.equals(check3));  // true
    System.out.println(net4.equals(check4));  // true
    System.out.println(net5.equals(check5));  // true
  }
}
