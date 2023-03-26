// Builder Design Pattern
#include <iostream>
#include <memory>
#include <assert.h>
#include <vector>
#include <string>
// The main idea behind the builder design pattern is
// to provide an abstract interface for a 'builder object'
// A concrete builder object is not a factory object which returns
// a ready-made object of a certain type. A concrete builder object
// should be viewed as a toolbox allowing someone else (that someone
// else is called 'a director' within the context of the builer design
// pattern) to build an object of some type according to some plan.

// Let us define a possible 'director' class, whose purpose
// it is to manufacture meals, together with an interface 'MealBuilder'

class MealBuilder{
  public:
  virtual ~MealBuilder(){}
  virtual void startNewMeal()=0;
  virtual void addBurger()=0;
  virtual void addDrink()=0;
};

typedef std::shared_ptr<MealBuilder> pMealBuilder;

class DirectorCook {
  pMealBuilder _builder;
  public:
  // A director is contructed from a builder, which specifies its toolbox
  DirectorCook(MealBuilder* builder):_builder(builder){}
  // This is the main method of the director, which creates an object
  // based on some logic and algorithm which is encapsulated in the
  // method body, and uses the tools provided by the builder interface.
  void makeMeal(){
    assert(_builder != nullptr);
    _builder->startNewMeal();
    _builder->addBurger();
    _builder->addDrink();
  }
};

// Note that the manufacture algorithm contained in the director
// is very general and does not tell us anything about the type of
// the object being created, let alone its internal representation.

// We can implement MealBuilder in many different ways, so as to 
// construct objects of many possible types which do not even need
// to be related by a common base class 'Meal'

// However, at some point we need to retrieve the constructed object
// so there must be some method 'getObject'. In general, because the
// return type of 'getObject' may be arbitrary, the method declaration
// cannot be part of the interface MealBuilder as this would constrain
// the implementation to a specific type being constructed.

// In this example, we shall consider two concrete implementations of
// MealBuilder, a 'VegetarianMealBuilder' and a 'NonVegetarianMealBuilder'.
// Both implementation will allow the construction of objects of the same
// type, but one should remember that this need not be the case when 
// applying the builder design pattern.

// Concrete implementations of MealBuilder will hold a pointer to object
// of type Meal (the object being constructed), and will have a getObject().

class Packing {
  public:
    virtual ~Packing(){}
    virtual std::string pack()=0;
};

typedef std::shared_ptr<Packing> pPacking;

class Wrapper : public Packing {
  public:
    std::string pack() override {return "Wrapper";}
};

class Bottle : public Packing {
  public:
    std::string pack() override {return "Bottle";}
};

class Item {
  public:
    virtual ~Item(){}
    virtual double price()=0;
    virtual std::string name()=0;
    virtual pPacking packing()=0;
};

class Burger: public Item {
  public:
    pPacking packing() override {return pPacking(new Wrapper());}
};

class ColdDrink: public Item {
  public:
    pPacking packing() override {return pPacking(new Bottle());}
};

class VegBurger: public Burger {
  public:
    double price() override {return 2.5;}
    std::string name() override {return "Veg Burger";}
};

class ChickenBurger: public Burger {
  public:
    double price() override {return 5.05;}
    std::string name() override {return "Chicken Burger";}
};

class Coke: public ColdDrink {
  public:
    double price() override {return 3.0;}
    std::string name() override {return "Coke";}
};

class Pepsi: public ColdDrink {
  public:
    double price() override {return 3.5;}
    std::string name() override {return "Pepsi";}
};

typedef std::shared_ptr<Item> pItem;

class Meal{
  std::vector<pItem> _items; // initially empty
  public:
  // This method is crucially needed for the implementation of both builders
  void addItem(pItem item){ _items.push_back(item);}
  // we define a few more methods to make this example more interesting
  double getCost(){
    double cost = 0.0;
    for(std::vector<pItem>::iterator i = _items.begin(); i != _items.end(); ++i){
      cost += (*i)->price();
    }
    return cost;
  }
  //
  void showItems(){
    for(std::vector<pItem>::iterator i = _items.begin(); i != _items.end(); ++i){
      std::cout << "Item : " << (*i)->name();
      std::cout << ", Packing : " << (*i)->packing()->pack();
      std::cout << ", Price : " << (*i)->price() << std::endl;
    }
 
  }
};

typedef std::shared_ptr<Meal> pMeal;

class VegetarianMealBuilder: public MealBuilder {
  pMeal _meal;
  public:
  // MealBuilder interface implementation
  void startNewMeal() override {_meal = pMeal(new Meal());}
  void addBurger() override {_meal->addItem(pItem(new VegBurger()));}
  void addDrink() override {_meal->addItem(pItem(new Coke()));}
  // the getObject method
  pMeal getMeal(){return _meal;}
};

class NonVegetarianMealBuilder: public MealBuilder {
  pMeal _meal;
  public:
  // MealBuilder interface implementation
  void startNewMeal() override {_meal = pMeal(new Meal());}
  void addBurger() override {_meal->addItem(pItem(new ChickenBurger()));}
  void addDrink() override {_meal->addItem(pItem(new Pepsi()));}
  // the getObject method
  pMeal getMeal(){return _meal;}
};

// let's try everything out
int main(int argc, char* argv[]){
  // creating vegetarian meal
  // First we create the appropriate concrete builder
  VegetarianMealBuilder* vegBuilder = new VegetarianMealBuilder();
  // Next we create a director which will use this builder
  DirectorCook cook(vegBuilder);  // cook has ownership of pointer
  // Next we let the cook prepare the meal
  cook.makeMeal();
  // Next we retrieve the object from the builder
  // Note here that we needed to declare vegBuilder specifically
  // of type 'VegetarianMealBuilder*', rather than 'MealBuilder*'
  // so we have access to the method 'getMeal' which is not part
  // of the 'MealBuilder' interface. Because both our concrete
  // builders in this example create objects of the same type
  // 'Meal', it is of course possible to declare getMeal as 
  // part of the MealBuilder interface. 
  pMeal vegMeal = vegBuilder->getMeal();
  // outputting result
  std::cout << "Veg Meal" << std::endl;
  vegMeal->showItems();
  std::cout << "Total Cost: " << vegMeal->getCost() << std::endl;

  // same for non-vegetarian meal
  NonVegetarianMealBuilder* nonVegBuilder = new NonVegetarianMealBuilder();
  cook = DirectorCook(nonVegBuilder); // default operator=() ok here
  cook.makeMeal();
  pMeal nonVegMeal = nonVegBuilder->getMeal();
  // outputting result
  std::cout << "\nNon-Veg Meal" << std::endl;
  nonVegMeal->showItems();
  std::cout << "Total Cost: " << nonVegMeal->getCost() << std::endl;

  return 0;
}

