import java.util.List;
import java.util.ArrayList;
import java.util.concurrent.Future;

import com.google.common.util.concurrent.ListenableFuture;

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
import org.bitcoinj.utils.Threading;

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


    // we can loop through peers the old-fashion way:
    System.out.println("Retrieving blockchain heights from peers ...");
    for(int i = 0; i < connectedPeers.size(); ++i){
      System.out.println("Chain height for " + connectedPeers.get(i) + " is " +
          connectedPeers.get(i).getBestHeight());
    }

    // or slightly more modern is:
    System.out.println("Measuring connection speeds ...");
    connectedPeers.forEach(peer -> { 
      // The get() call forces the program to wait for the ping.
      // Peers are pinged in the background and the ping times averaged.
      // If we don't wait here, we may not get a realistic ping time back
      // as program just started (????)
      try{
        peer.ping().get();
      } catch (Exception e){
        System.err.println("Exception caught while calling ping on peer");
      }
      System.out.println("Ping time for " + peer + " is " +
          peer.getLastPingTime());
    });
 
    
  // bitcoinj is a threaded library. This means you can freely 
  // run code in parallel and mix and match concurrent constructs to 
  // use your preferred style. Above we used blocking code. This is 
  // convenient in scripts and so on, but sometimes we want to keep 
  // the main thread free. Let's do the same thing but in an async style:
  System.out.println("Measuring connection speed asynchronously ...");
  List<Future<Long>> futures = new ArrayList<>();
  connectedPeers.forEach(peer -> {
    ListenableFuture<Long> future = peer.ping();
    futures.add(future);

    // a 'future' is sometimes called a promise. this construct says: 
    // run the closure on the 'user thread' when the future completes. 
    // we can get the result using future.get() which won't block 
    // because we know it's now ready.
    // the user thread is a thread that sits around waiting for closures 
    // to be given to it and then runs them in sequence. so by specifying 
    // user_thread here we know the closure cannot run in parallel. we 
    // could ask the closure to run on other threads too, if we wanted, 
    // e.g. the javafx ui thread if making a gui app.

    future.addListener(() -> {
      Long pingTime = null;
      try {
        pingTime = future.get();
      } catch (Exception e){
        System.err.println("Exception caught while asynch ping");
      }
      System.out.println("Async callback ping time for " + 
          peer + " is " + pingTime);}, Threading.USER_THREAD);
  });


  System.out.println("Waiting for all peers to respond ...");
  futures.forEach(f -> {
    try {
      f.get();
    } catch (Exception e){
      System.err.println("Exception caught while waiting for peers");
    }
  });

  
  System.out.println("Done!");
  }
}
