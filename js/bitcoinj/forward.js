var bcj = org.bitcoinj;
var params = bcj.params.TestNet3Params.get();


// Address where we'll send received coins (minus the miner fee)
var FORWARD_TO = "mfZCyhQUQXy2S91hnGepdaJxfaNjMg15AV";

// Make logging more compact
bcj.utils.BriefLogFormatter.init();

var Address = bcj.core.Address;
var fwdAddress = new Address(params, FORWARD_TO);

print(FORWARD_TO);  // "mfZCyhQUQXy2S91hnGepdaJxfaNjMg15AV"
print(fwdAddress);  // "mfZCyhQUQXy2S91hnGepdaJxfaNjMg15AV"


var File = java.io.File
var dir = new File(".");

var WalletAppKit = bcj.kits.WalletAppKit;
var kit = new WalletAppKit(params, dir, "forward-demo");

print("Staring up ...");
kit.startAsync();
print("Waiting ...");
kit.awaitRunning();


