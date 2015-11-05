#include <iostream>
#include <string> // std::string
#include <memory> // std::shared_ptr<T>
#include <boost/algorithm/string/predicate.hpp> // boost::iequals

class IShape {
  public:
  virtual ~IShape(){}
  virtual void draw() const = 0;
};

class Rectangle : public IShape {

  public:
  void draw() const override {
    std::cout << "Inside Rectangle::draw() method.\n";
  }
};

class Square : public IShape {

  public:
  void draw() const override {
    std::cout << "Inside Square::draw() method.\n";
  }
};

class Circle : public IShape {

  public:
  void draw() const override {
    std::cout << "Inside Circle::draw() method.\n";
  }
};

class ShapeFactory {
  // use getShape method to get object of type IShape
  public:
    std::shared_ptr<IShape> getShape(std::string shapeType){

    if(shapeType.empty()){
      return nullptr;
    }

    if(boost::iequals(shapeType,"CIRCLE")){
        return std::shared_ptr<IShape>(new Circle());
    } else if(boost::iequals(shapeType,"RECTANGLE")){
        return std::shared_ptr<IShape>(new Rectangle());
    } else if(boost::iequals(shapeType,"SQUARE")){
        return std::shared_ptr<IShape>(new Square());
    }  

    return nullptr;
  }

};





int main(int argc, char* argv[]){
  ShapeFactory shapeFactory;

  // get an object of Circle and call its draw method.
  std::shared_ptr<IShape> shape1 = shapeFactory.getShape("CIRCLE");
  shape1->draw();

  // get an object of Rectangle and call its draw method.
  std::shared_ptr<IShape> shape2 = shapeFactory.getShape("RECTANGLE");
  shape2->draw();


  // get an object of Square and call its draw method.
  std::shared_ptr<IShape> shape3 = shapeFactory.getShape("SQUARE");
  shape3->draw();

  return 0;
}

