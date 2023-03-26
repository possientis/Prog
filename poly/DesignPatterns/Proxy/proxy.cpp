// Proxy Design Pattern
#include <iostream>
#include <iomanip>  // setprecision
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
class ComponentPrice {
  public:
   virtual ~ComponentPrice(){} 
   virtual double getCpuPrice() const = 0;
   virtual double getRamPrice() const = 0;
   virtual double getSsdPrice() const = 0;
};

// This is the real subject
class StoredComponentPrice : public ComponentPrice {
  public:
    ~StoredComponentPrice(){}
    double getCpuPrice() const override { return 250.0; }
    double getRamPrice() const override { return 32.0; }
    double getSsdPrice() const override { return 225.0; }
};

typedef enum { CPU=0, RAM=1, SSD=2} Request;
std::ostream& operator<<(std::ostream& s, Request request){
  switch(request){
    case CPU:
      s << "CPU"; break;
    case RAM:
      s << "RAM"; break;
    case SSD:
      s << "SSD"; break;
    default:
      s << "???"; break;
  }
  return s;
}

class Server {
  private:
    static Server* _server;
    Server(){}
  public:
    ~Server(){}
    static void startServer();
    static void stopServer();
    static Server* getInstance();
    double sendRequest(Request request);
};

Server* Server::_server = nullptr;

void Server::startServer(){
  _server = new Server();
  std::cout << "Component price server running, awaiting request\n";
}

void Server::stopServer(){ delete _server; _server == nullptr; }

Server* Server::getInstance(){
  if(_server == nullptr) startServer();
  return _server;
} 

double Server::sendRequest(Request request){
  std::cout << "Server receiving request for " << request << " price\n";
  // In our example, server uses real subject
  StoredComponentPrice component;   // real subject
  std::cout << "Server responding to request for " << request << " price\n";
  switch(request){
    case CPU:
      return component.getCpuPrice();
    case RAM:
      return component.getRamPrice();
    case SSD:
      return component.getSsdPrice();
    default:
      throw new std::exception();
  }
}

// This is the proxy
class ProxyComponentPrice : public ComponentPrice {
  public:
    ~ProxyComponentPrice(){}
    double getCpuPrice() const override { return requestFromServer(CPU); }
    double getRamPrice() const override { return requestFromServer(RAM); }
    double getSsdPrice() const override { return requestFromServer(SSD); }
  private:
    double requestFromServer(Request request) const {
      return Server::getInstance()->sendRequest(request);
    }
};

int main(){
  Server::startServer();
  // we can use proxy as if it was real, making client code a lot simpler
  ProxyComponentPrice prices;
  double cpu = prices.getCpuPrice();
  double ram = prices.getRamPrice();
  double ssd = prices.getSsdPrice();
  std::cout << "The CPU price is " << std::fixed << std::setprecision(1) 
            << cpu << std::endl;
  std::cout << "The RAM price is " << std::fixed << std::setprecision(1) 
            << ram << std::endl;
  std::cout << "The SSD price is " << std::fixed << std::setprecision(1) 
            << ssd << std::endl;
  Server::stopServer();

  return 0;
}
