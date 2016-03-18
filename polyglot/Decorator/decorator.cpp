// Decorator Design Pattern
#include <iostream>
#include <iomanip>  // std::setprecision
#include <string>
#include <assert.h>


// interface or abstract class of components
class Pizza {
  protected:
    Pizza(){}
  public:
    virtual ~Pizza(){}
    virtual std::string getDescription() const = 0;
    virtual double getCost() const = 0;
};

// concrete component
class PlainPizza : public Pizza {
  public:
    PlainPizza();
    virtual std::string getDescription() const override { return "Plain pizza"; }
    virtual double getCost() const override { return 3.0; }
    virtual ~PlainPizza();
};

PlainPizza::PlainPizza(){
//  std::cerr << "Creating pizza " << std::hex << this << std::endl;
}

PlainPizza::~PlainPizza(){
//  std::cerr << "Deleting pizza " << std::hex << this << std::endl;
}
// root abstract class of decorators implementing component interface
// a decorator object is therefore a component and will hold a 
// concrete component as data member. Default implementation
// achieved simply by forwarding 

class PizzaDecorator : public Pizza {
  protected:
    const Pizza* _pizza;
  public:
    PizzaDecorator(Pizza* pizza): _pizza(pizza){ assert(_pizza != nullptr); }
    virtual std::string getDescription() const override;
    virtual double getCost() const override;
    virtual ~PizzaDecorator();
};

// default implementation
std::string PizzaDecorator::getDescription() const {
  return _pizza->getDescription();
}

// default implementation
double PizzaDecorator::getCost() const {
  return _pizza->getCost();
}

PizzaDecorator::~PizzaDecorator(){
  delete _pizza;
}

// first concrete decorator
class WithExtraCheese : public PizzaDecorator {
  public:
    WithExtraCheese(Pizza* pizza) : PizzaDecorator(pizza) {}
    virtual std::string getDescription() const override;
    virtual double getCost() const override;
    virtual ~WithExtraCheese(){}
};

std::string WithExtraCheese::getDescription() const {
  return _pizza->getDescription() + " + extra cheese";
}

double WithExtraCheese::getCost() const {
  return _pizza->getCost() + 0.5;
}

// second concrete decorator
class WithExtraOlives : public PizzaDecorator {
  public:
    WithExtraOlives(Pizza* pizza) : PizzaDecorator(pizza) {}
    virtual std::string getDescription() const override;
    virtual double getCost() const override;
    virtual ~WithExtraOlives(){}
};

std::string WithExtraOlives::getDescription() const {
  return _pizza->getDescription() + " + extra olives";
}

double WithExtraOlives::getCost() const {
  return _pizza->getCost() + 0.7;
}

// third concrete decorator
class WithExtraAnchovies : public PizzaDecorator {
  public:
    WithExtraAnchovies(Pizza* pizza) : PizzaDecorator(pizza) {}
    virtual std::string getDescription() const override;
    virtual double getCost() const override;
    virtual ~WithExtraAnchovies(){}
};

std::string WithExtraAnchovies::getDescription() const {
  return _pizza->getDescription() + " + extra anchovies";
}

double WithExtraAnchovies::getCost() const {
  return _pizza->getCost() + 0.8;
}

int main(){

  Pizza* plainPizza = new PlainPizza();

  Pizza* nicePizza  = new WithExtraCheese(
                      new PlainPizza());

  Pizza* superPizza = new WithExtraOlives(
                      new WithExtraCheese(
                      new PlainPizza())); 

  Pizza* ultraPizza = new WithExtraAnchovies( 
                      new WithExtraOlives(
                      new WithExtraCheese(
                      new PlainPizza()))); 

  std::cout << "Plain Pizza: "    << std::fixed << std::setprecision(1) 
            << "\tCost: "         << plainPizza->getCost() 
            << "\tDescription: "  << plainPizza->getDescription() << std::endl; 

  std::cout << "Nice Pizza: "     << std::fixed << std::setprecision(1) 
            << "\tCost: "         << nicePizza->getCost() 
            << "\tDescription: "  << nicePizza->getDescription() << std::endl; 

  std::cout << "Super Pizza: "    << std::fixed << std::setprecision(1) 
            << "\tCost: "         << superPizza->getCost() 
            << "\tDescription: "  << superPizza->getDescription() << std::endl; 

  std::cout << "Ultra Pizza: "    << std::fixed << std::setprecision(1) 
            << "\tCost: "         << ultraPizza->getCost() 
            << "\tDescription: "  << ultraPizza->getDescription() << std::endl; 
  
  delete ultraPizza;
  delete superPizza;
  delete nicePizza;
  delete plainPizza;

  return 0;
}

