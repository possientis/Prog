// Proxy Design Pattern
using System;
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
  double CpuPrice { get; }
  double RamPrice { get; }
  double SsdPrice { get; }
}

// This is the real subject
class StoredComponentPrice : ComponentPrice {
  public double CpuPrice  { get { return 250.0; } }   // accessing some local DB
  public double RamPrice  { get { return 32.0;  } }   // accessing some local DB
  public double SsdPrice  { get { return 225.0; } }   // accessing some local DB
}
//
// This is the proxy
class ProxyComponentPrice : ComponentPrice {
  public double CpuPrice  { get { return RequestFromServer("CPU"); } }
  public double RamPrice  { get { return RequestFromServer("RAM"); } }
  public double SsdPrice  { get { return RequestFromServer("SSD"); } }

  private double RequestFromServer(String request){
    return Server.GetInstance().SendRequest(request);
  }
}

class Server {
  private static readonly Server server = new Server();
  private Server(){ 
    Console.WriteLine("Component price server running, awaiting request");
  }
  public static Server GetInstance(){ return server; }
  public double SendRequest(String request){
    Console.WriteLine("Server receiving request for {0} price", request);

    // In our example, server uses real subject
    ComponentPrice component = new StoredComponentPrice();  // real subject
   
    Console.WriteLine("Server responding to request for {0} price", request);
    switch(request){
      case "CPU":
        return component.CpuPrice;
      case "RAM":
        return component.RamPrice;
      case "SSD":
        return component.SsdPrice;
      default:
        throw new InvalidOperationException();
    } 
  }
}

public class Proxy {
  public static void Main(string[] args){
    // we can use proxy as if it was real, making client code a lot simpler
    ComponentPrice prices = new ProxyComponentPrice();
    double cpu = prices.CpuPrice;
    double ram = prices.RamPrice;
    double ssd = prices.SsdPrice;
    Console.WriteLine("The CPU price is {0:0.0}", cpu);
    Console.WriteLine("The RAM price is {0:0.0}", ram);
    Console.WriteLine("The SSD price is {0:0.0}", ssd);
  }
}
