// import some stuff
var bcj = org.bitcoinj;
var ECKey = bcj.core.ECKey;


// We'll use the tesnet for now
var params  = bcj.params.TestNet3Params.get();
var key = new ECKey();

print(key);



