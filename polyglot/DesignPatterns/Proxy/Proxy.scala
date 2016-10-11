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

// This is the subject
trait ComponentPrice {
  def CpuPrice : Double
  def RamPrice : Double
  def SsdPrice : Double
}

// This is the real subject
class StoredComponentPrice extends ComponentPrice {
  def CpuPrice = 250.0
  def RamPrice = 32.0
  def SsdPrice = 225.0
}

// This is the proxy
class ProxyComponentPrice extends ComponentPrice {
  def CpuPrice = requestFromServer(Server.CPU)
  def RamPrice = requestFromServer(Server.RAM)
  def SsdPrice = requestFromServer(Server.SSD)
  
  def requestFromServer(request : Server.Request) : Double = 
    Server.sendRequest(request)
 
}

object Server {
  
  println("Component price server running, awaiting request")

  abstract class Request
  case object CPU extends Request { override def toString = "CPU" }
  case object RAM extends Request { override def toString = "RAM" }
  case object SSD extends Request { override def toString = "SSD" }

  def sendRequest(request: Request) = {
    println("Server receiving request for " + request + " price")
    // In our example, server uses real subject
    val component = new StoredComponentPrice  // real subject
    println("Server responding to request for " + request + " price")
    request match {
      case  CPU => component.CpuPrice
      case  RAM => component.RamPrice
      case  SSD => component.SsdPrice
      case    _ => throw new Exception() 
    } 
  }
}

object Proxy {
  def main(args: Array[String]){
    // we can use proxy as if it was real, making client code a lot simpler
    val prices = new ProxyComponentPrice()
    val cpu = prices.CpuPrice
    val ram = prices.RamPrice
    val ssd = prices.SsdPrice
    println("The CPU price is " + cpu);
    println("The RAM price is " + ram);
    println("The SSD price is " + ssd);
  }
}
