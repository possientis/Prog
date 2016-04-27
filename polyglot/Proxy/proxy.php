<?php
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
interface ComponentPrice {
  public function getCpuPrice();
  public function getRamPrice();
  public function getSsdPrice();
}

// This is the real subject
class StoredComponentPrice implements ComponentPrice {
  public function getCpuPrice(){ return 250.0; }  // accessing some local DB
  public function getRamPrice(){ return 32.0;  }  // accessing some local DB
  public function getSsdPrice(){ return 225.0; }  // accessing some local DB
}

// This is the proxy
class ProxyComponentPrice implements ComponentPrice {
  public function getCpuPrice(){ return $this->requestFromServer("CPU"); }
  public function getRamPrice(){ return $this->requestFromServer("RAM"); }
  public function getSsdPrice(){ return $this->requestFromServer("SSD"); }

  public function requestFromServer($request){
    return Server::getInstance()->sendRequest($request);
  }
}

class Server {
  static private $server;
  static public function startServer(){ Server::$server = new Server; }
  static public function getInstance(){ return Server::$server; }
  public function __construct(){
    echo "Component price server running, awaiting request\n";
  }
  public function sendRequest($request){
    echo "Server receiving request for {$request} price\n";
    // In our example, server uses real subject
    $component = new StoredComponentPrice;  // real subject
    echo "Server responding to request for {$request} price\n";
    switch($request){
    case "CPU":
      return $component->getCpuPrice();
    case "RAM":
      return $component->getRamPrice();
    case "SSD":
      return $component->getSsdPrice();
    default:
      throw new Exception;
    }
  }
}

Server::startServer();
// we can use proxy as it it was real, making client clode a lot simpler
$prices = new ProxyComponentPrice;
$cpu = $prices->getCpuPrice();
$ram = $prices->getRamPrice();
$ssd = $prices->getSsdPrice();
echo "The CPU price is ".number_format($cpu,1)."\n";
echo "The RAM price is ".number_format($ram,1)."\n";
echo "The SSD price is ".number_format($ssd,1)."\n";

?>

