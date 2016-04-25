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
  double getCpuPrice();
  double getRamPrice();
  double getSsdPrice();
}

// This is the real subject
class StoredComponentPrice implements ComponentPrice {
  public double getCpuPrice(){ return 250.0; }  // accessing some local DB
  public double getRamPrice(){ return 32.0; }   // accessing some local DB
  public double getSsdPrice(){ return 225.0; }  // accessing some local DB
}
//
// This is the proxy
class ProxyComponentPrice implements ComponentPrice {
  public double getCpuPrice(){ return requestFromServer("CPU"); }
  public double getRamPrice(){ return requestFromServer("RAM"); }
  public double getSsdPrice(){ return requestFromServer("SSD"); }

  private double requestFromServer(String request){
    return Server.getInstance().sendRequest(request);
  }
}

class Server {
  private static final Server server = new Server();
  private Server(){ 
    System.out.println("Component price server running, awaiting request");
  }
  public static Server getInstance(){ return server; }
  public double sendRequest(String request){
    System.out.println("Server receiving request for " + request + " price");
    // In our example, server uses real subject
    ComponentPrice component = new StoredComponentPrice();  // real subject
    System.out.println("Server responding to request for " + request + " price");
    switch(request){
      case "CPU":
        return component.getCpuPrice();
      case "RAM":
        return component.getRamPrice();
      case "SSD":
        return component.getSsdPrice();
      default:
        throw new UnsupportedOperationException();
    } 
  }
}

public class Proxy {
  public static void main(String[] args){
    // we can use proxy as if it was real, making client code a lot simpler
    ComponentPrice prices = new ProxyComponentPrice();
    double cpu = prices.getCpuPrice();
    double ram = prices.getRamPrice();
    double ssd = prices.getSsdPrice();
    System.out.println("The CPU price is " + cpu);
    System.out.println("The RAM price is " + ram);
    System.out.println("The SSD price is " + ssd);
  }
}
