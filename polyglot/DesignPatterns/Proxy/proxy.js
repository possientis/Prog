// Proxy Design Pattern
//
// This code exercise is borrowed from Design Patterns in C# - 13 Proxy 
// https://www.youtube.com/watch?v=XvbDqLrnkmA

// A proxy is a class which functions as an interface to something else

// There are three participants to the proxy design pattern:
//
// 1. subject
// 2. real subject
// 3. proxy
//

// The subject is the common interface between the real object and proxy
// the real object is that which the proxy is meant to be substituted for

// This is the subject
function ComponentPrice(){}
ComponentPrice.prototype.getCpuPrice = function(){ throw "Not implemented"; }
ComponentPrice.prototype.getRamPrice = function(){ throw "Not implemented"; }
ComponentPrice.prototype.getSsdPrice = function(){ throw "Not implemented"; }


// This is the real subject
function StoredComponentPrice(){} // skipping class derivation boiler plate
StoredComponentPrice.prototype.getCpuPrice = function(){ return 250.0; }
StoredComponentPrice.prototype.getRamPrice = function(){ return 32.0; }
StoredComponentPrice.prototype.getSsdPrice = function(){ return 225.0; }

// This is the proxy
function ProxyComponentPrice(){}  // skipping class derivation boiler plate
ProxyComponentPrice.prototype.getCpuPrice = function(){ 
  return this.requestFromServer("CPU");
}
ProxyComponentPrice.prototype.getRamPrice = function(){ 
  return this.requestFromServer("RAM");
}
ProxyComponentPrice.prototype.getSsdPrice = function(){ 
  return this.requestFromServer("SSD");
}
ProxyComponentPrice.prototype.requestFromServer = function(request){
  return Server.getInstance().sendRequest(request);
}

function Server(){
  console.log("Component price server running, awaiting request");
}
Server.startServer = function(){ Server._server = new Server(); }
Server.getInstance = function(){ return Server._server; }
Server.prototype.sendRequest = function(request){
  console.log("Server receiving request for " + request + " price");
  // In our example, server uses real subject
  var component = new StoredComponentPrice(); // real subject
  console.log("Server responding to request for " + request + " price");
  switch(request){
    case "CPU":
      return component.getCpuPrice();
    case "RAM":
      return component.getRamPrice();
    case "SSD":
      return component.getSsdPrice();
    default:
      throw "Invalid request";
  }
}

Server.startServer();
// we can use proxy as if it was real, making client code a lot simpler
var prices = new ProxyComponentPrice();
var cpu = prices.getCpuPrice();
var ram = prices.getRamPrice();
var ssd = prices.getSsdPrice();
console.log("The CPU price is " + cpu.toFixed(1));
console.log("The RAM price is " + ram.toFixed(1));
console.log("The SSD price is " + ssd.toFixed(1));






