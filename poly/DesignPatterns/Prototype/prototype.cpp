// Prototype design pattern
// Imagine that in order to instantiate certain objects we need to carry out
// expensive database queries. In order to improve performance, it would 
// be beneficial to cache whatever object is created from the database
// and return a copy of the cached object whenever a subsequent request
// for object instantiation arises.

#include <iostream>
#include <memory>
#include <string>
#include <map>

class Cloneable;
typedef std::shared_ptr<Cloneable> pCloneable;
class Cloneable {
  public:
    virtual ~Cloneable(){};
    virtual pCloneable clone() const =0;
};

class Shape : public Cloneable {

  std::string id;

  public:
    virtual ~Shape(){};
    virtual void draw() const =0;
    virtual pCloneable clone() const =0;
    std::string get_id() const {return id;}
    void set_id(std::string id){this->id = id;}
};

typedef std::shared_ptr<Shape> pShape;
class Rectangle : public Shape {
  public:
    ~Rectangle(){}
    void draw() const override {
      std::cout << "Inside Rectangle::draw() method.\n";
    }
    pCloneable clone() const override {
      pShape clone = pShape(new Rectangle());
      clone->set_id(this->get_id());
      return clone;
    }
};

class Square : public Shape {
  public:
    ~Square(){}
    void draw() const override {
      std::cout << "Inside Square::draw() method.\n";
    }
    pCloneable clone() const override {
      pShape clone = pShape(new Square());
      clone->set_id(this->get_id());
      return clone;
    }
};

class Circle : public Shape {
  public:
    ~Circle(){}
    void draw() const override {
      std::cout << "Inside Circle::draw() method.\n";
    }
    pCloneable clone() const override {
      pShape clone = pShape(new Circle());
      clone->set_id(this->get_id());
      return clone;
    }
};


class PrototypeManager {

  std::map<std::string,pShape> shapeMap;

  public:
    ~PrototypeManager(){};
    pShape get_shape(std::string id){
      pShape cachedShape = shapeMap[id];
      return std::dynamic_pointer_cast<Shape>(cachedShape->clone());
    }
    void load_cache(){
      pShape rect = pShape(new Rectangle());
      rect->set_id("1");
      shapeMap[rect->get_id()] = rect;

      pShape square = pShape(new Square());
      square->set_id("2");
      shapeMap[square->get_id()] = square;

      pShape circle = pShape(new Circle());
      circle->set_id("3");
      shapeMap[circle->get_id()] = circle;
    }
};

int main(int argc, char* argv[]){

  // need a prototype manager
  PrototypeManager manager;
  // prototype manager regusters a few prototypes
  manager.load_cache();
  // prototype manager can now be used as factory object
  pShape cloned_shape1 = manager.get_shape("1");
  cloned_shape1->draw();

  pShape cloned_shape2 = manager.get_shape("2");
  cloned_shape2->draw();

  pShape cloned_shape3 = manager.get_shape("3");
  cloned_shape3->draw();

  return 0;

}
