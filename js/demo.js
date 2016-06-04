// jjs -cp the-bitcoinj.jar:the-slf4j.jar myfile 

// import some stuff
var bcj = org.bitcoinj;
var ECKey = bcj.core.ECKey;


// We'll use the tesnet for now
var params  = bcj.params.TestNet3Params.get();
var key = new ECKey();

// conversion to address will be different, depending on whether we are on 
// testing network or real network.

var address = key.toAddress(params);
print(address);







