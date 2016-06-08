// jjs -cp the-bitcoinj.jar:the-slf4j.jar myfile 

// import some stuff
var bcj = org.bitcoinj;
var ECKey = bcj.core.ECKey;


// We'll use the tesnet for now
var params  = bcj.params.TestNet3Params.get();

// Most basic operation: make a key and print its address for to the screen
var key = new ECKey();

// conversion to address will be different, depending on whether we are on 
// testing network or real network.

var address = key.toAddress(params);
print(address);


// Keys record their creation time. Java getFoo()/setFoo() style methods 
// can be treated as js properties:
print(key.creationTimeSeconds);
key.creationTimeSeconds = 0;
print(key.creationTimeSeconds);


// The default logging output format when using JDK logging is a bit verbose 
// (two lines per log entry!), so let's fix that here to be a bit more compact.
bcj.utils.BriefLogFormatter.init();


// Let's connect to the network. This won't download the block chain.
var PeerGroup = bcj.core.PeerGroup;
print("Creating peer group");
var pg = new PeerGroup(params);

var DnsDiscovery = bcj.net.discovery.DnsDiscovery;
print("Creating discovery object");
var discovery = new DnsDiscovery(params);

print("Adding discovery object to peer group");
pg.addPeerDiscovery(discovery);
print("Starting peer group");
pg.start();

// Wait until we have at least three peers.
print("Waiting for some peers");
pg.waitForPeers(3).get();
print("Connected to: " + pg.connectedPeers);


// Let's print out their subVer (sort of like an http user agent). 
// connectedPeers is a Java collection which can be treated like a 
// Javascript array. Nashorn implements a small extension to 
// Javascript to make iteration easier, the "for each" construct:
print("Retrieving connected peers collection");
var connectedPeers = pg.connectedPeers;

for each (var peer in connectedPeers)
  print(peer.peerVersionMessage.subVer);
/*
  /Satoshi:0.11.2/
  /Satoshi:0.11.2/
  /Satoshi:0.11.0/
*/

// Of course we can do it the old-fashioned way:
for(var i = 0; i  < connectedPeers.length; ++i){
  print("Chain height for " + connectedPeers[i] + " is " + 
          connectedPeers[i].bestHeight);
}

// or slightly more modern is:
connectedPeers.forEach(function(peer) {
  // The get() call forces the program to wait for the ping.
  // Peers are pinged in the background and the ping times averaged.
  // If we don't wait here, we may not get a realistic ping time back
  // as program just started (????)
  peer.ping().get();
  print("Ping time for " + peer + " is " + peer.lastPingTime);
});


// Nashorn, unlike V8, is thread safe (because it runs on the JVM). 
// And bitcoinj is a threaded library. This means you can freely 
// run code in parallel and mix and match concurrent constructs to 
// use your preferred style. Above we used blocking code. This is 
// convenient in scripts and so on, but sometimes we want to keep 
// the main thread free. Let's do the same thing but in an async style:




















