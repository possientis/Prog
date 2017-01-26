import java.math.BigInteger;
import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.core.ECKey.ECDSASignature;
import org.bitcoinj.core.Utils;

class Test16 {
  public static void main(String[] args)
  {

    String[] strPriv = {
      "1", 
      "1", 
      "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140", 
      "f8b8af8ce3c7cca5e300d33939540c10d45ce001b8f252bfbc57ba0342904181",
      "e91671c46231f833a6406ccbea0e3e392c76c167bac1cb013f6f1013980455c2"
    };

    String[] strMsg = {
      "Satoshi Nakamoto",
      "All those moments will be lost in time, like tears in rain. Time to die...",
      "Satoshi Nakamoto",
      "Alan Turing",
      "There is a computer disease that anybody who works with computers knows about."
    + " It's a very serious disease and it interferes completely with the work."
    + " The trouble with computers is that you 'play' with them!"
    };

    String[] strKey = {
      "0x8F8A276C19F4149656B280621E358CCE24F5F52542772691EE69063B74F15D15",
      "0x38AA22D72376B4DBC472E06C3BA403EE0A394DA63FC58D88686C611ABA98D6B3",
      "0x33A19B60E25FB6F4435AF53A3D42D493644827367E6453928554F43E49AA6F90",
      "0x525A82B70E67874398067543FD84C83D30C175FDC45FDEEE082FE13B1D7CFDF1",
      "0x1F4B84C23A86A221D233F2521BE018D9318639D5B8BBD6374A8A59232D16AD3D"
    };

    String[] strSig = {
      "934b1ea10a4b3c1757e2b0c017d0b6143ce3c9a7e6a4a49860d7a6ab210ee3d8"
    + "2442ce9d2b916064108014783e923ec36b49743e2ffa1c4496f01a512aafd9e5",
      "8600dbd41e348fe5c9465ab92d23e3db8b98b873beecd930736488696438cb6b"
    + "547fe64427496db33bf66019dacbf0039c04199abb0122918601db38a72cfc21",
      "fd567d121db66e382991534ada77a6bd3106f0a1098c231e47993447cd6af2d0"
    + "6b39cd0eb1bc8603e159ef5c20a5c8ad685a45b06ce9bebed3f153d10d93bed5",
      "7063ae83e7f62bbb171798131b4a0564b956930092b33b07b395615d9ec7e15c"
    + "58dfcc1e00a35e1572f366ffe34ba0fc47db1e7189759b9fb233c5b05ab388ea",
      "b552edd27580141f3b2a5463048cb7cd3e047b97c9f98076c32dbdf85a68718b"
    + "279fa72dd19bfae05577e06c7c0c1900c371fcd5893f7e1d56a37d30174671f6"
    };

/*
  r = 934b1ea10a4b3c1757e2b0c017d0b6143ce3c9a7e6a4a49860d7a6ab210ee3d8
  s = 2442ce9d2b916064108014783e923ec36b49743e2ffa1c4496f01a512aafd9e5
  r = 8600dbd41e348fe5c9465ab92d23e3db8b98b873beecd930736488696438cb6b
  s = 547fe64427496db33bf66019dacbf0039c04199abb0122918601db38a72cfc21
  r = fd567d121db66e382991534ada77a6bd3106f0a1098c231e47993447cd6af2d0
  s = 6b39cd0eb1bc8603e159ef5c20a5c8ad685a45b06ce9bebed3f153d10d93bed5
  r = 7063ae83e7f62bbb171798131b4a0564b956930092b33b07b395615d9ec7e15c
  s = 58dfcc1e00a35e1572f366ffe34ba0fc47db1e7189759b9fb233c5b05ab388ea
  r = b552edd27580141f3b2a5463048cb7cd3e047b97c9f98076c32dbdf85a68718b
  s = 279fa72dd19bfae05577e06c7c0c1900c371fcd5893f7e1d56a37d30174671f6
*/

/*    
  r = 934b1ea10a4b3c1757e2b0c017d0b6143ce3c9a7e6a4a49860d7a6ab210ee3d8
  s = dbbd3162d46e9f9bef7feb87c16dc13b4f6568a87f4e83f728e2443ba586675c
  r = 8600dbd41e348fe5c9465ab92d23e3db8b98b873beecd930736488696438cb6b
  s = ab8019bbd8b6924cc4099fe625340ffb1eaac34bf4477daa39d0835429094520
  r = fd567d121db66e382991534ada77a6bd3106f0a1098c231e47993447cd6af2d0
  s = 94c632f14e4379fc1ea610a3df5a375152549736425ee17cebe10abbc2a2826c
  r = 7063ae83e7f62bbb171798131b4a0564b956930092b33b07b395615d9ec7e15c
  s = a72033e1ff5ca1ea8d0c99001cb45f0272d3be7525d3049c0d9e98dc7582b857
  r = b552edd27580141f3b2a5463048cb7cd3e047b97c9f98076c32dbdf85a68718b
  s = 279fa72dd19bfae05577e06c7c0c1900c371fcd5893f7e1d56a37d30174671f6
*/
    // retrieving private keys
    BigInteger[] priv = new BigInteger[5];
    for(int i = 0; i < 5; ++i) {
      priv[i] = new BigInteger(strPriv[i],16);
    }

    // computing single hashes of messages
    Sha256Hash[] hash = new Sha256Hash[5];
    for(int i = 0; i < 5; ++i) {
      hash[i] = Sha256Hash.of(strMsg[i].getBytes());
    }

    // computing deterministic k's from private keys and single hashes
    BigInteger[] expected = new BigInteger[5];
    for(int i = 0; i < 5; ++i) {
      expected[i] = EC_Test_Utils.getDeterministicKey(priv[i], hash[i], 0);
//      System.out.println(expected[i].toString(16));
    }

    // computing signatures
    ECDSASignature[] sig = new ECDSASignature[5];
    for(int i = 0; i < 5; ++i) {
      byte[] bytes = Utils.bigIntegerToBytes(priv[i], 32); 
      sig[i] = EC_Test_Utils.signCheck(hash[i], bytes);
      System.out.println("r = " + sig[i].r.toString(16));
      System.out.println("s = " + sig[i].s.toString(16));
    }
  }
}

