import java.util.List;

// core classes
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.Address;
import org.bitcoinj.core.PeerGroup;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Peer;

// network parameters classes
import org.bitcoinj.params.TestNet3Params;

// utility classes
import org.bitcoinj.utils.BriefLogFormatter;

// network classes
import org.bitcoinj.net.discovery.DnsDiscovery;

public class Demo {
  public static void main(String[] args){

    // we'll use the tesnet network for now
    System.out.println("Retrieving testnet network ...");
    NetworkParameters params = TestNet3Params.get(); 

    // most basic operation: make a key and print its address for the screen
    System.out.println("Creating new key ...");
    ECKey key = new ECKey();

    // Conversion of key ot address depends on network type 
    System.out.println("Retrieving corresponding address ...");
    Address address = key.toAddress(params);
    System.out.println("Address = " + address);

    // keys record their creation time
    System.out.println("Key creation time = " + key.getCreationTimeSeconds());
    System.out.println("Setting creation time to zero ...");
    key.setCreationTimeSeconds(0);
    System.out.println("Key creation time = " + key.getCreationTimeSeconds());


    // The default logging output format when using JDK logging is a bit verbose 
    // (two lines per log entry!), so let's fix that here to be a bit more compact.
    System.out.println("Initializing log ...");
    BriefLogFormatter.init();


    // Let's connect to the network. This won't download the block chain.
    System.out.println("Creating new peer group ...");
    PeerGroup pg = new PeerGroup(params);

    System.out.println("Creating discovery object ...");
    DnsDiscovery discovery = new DnsDiscovery(params);

    System.out.println("Adding discovery object to peer group ...");
    pg.addPeerDiscovery(discovery);

    System.out.println("Starting peer group ...");
    pg.start();

    // Wait until we have at least three peers.
    System.out.println("Waiting for some peers ...");
    try {
      pg.waitForPeers(3).get();
    } catch (Exception e){
      System.err.println("Exception caught but ignored ...");
    }

    System.out.println("Retrieving list of connected peers ...");
    List<Peer> connectedPeers = pg.getConnectedPeers();
    System.out.println("Connected to: " + connectedPeers);
    
    System.out.println("Retrieving peer versions ...");
    for(Peer peer : connectedPeers){
      System.out.println(peer.getPeerVersionMessage().subVer);
    }
    




  }
}
