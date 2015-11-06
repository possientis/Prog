// the Abstract Factory pattern looks like the factory pattern 
// applied to the production of various factories
#include <iostream>
#include <string> // std::string
#include <memory> // std::shared_ptr<T>
#include <boost/algorithm/string/predicate.hpp> // boost::iequals

class IShape {
  public:
  virtual ~IShape(){}
  virtual void draw() const = 0;
};

class AbstractShape : public IShape {
  public:
  enum COLOR {RED,GREEN,BLUE};
  AbstractShape(COLOR color):mColor(color){}
  virtual ~AbstractShape(){}
  virtual void draw() const =0;
  protected:
  static std::string asString(COLOR color){
    switch(color){
      case RED:
        return "red";
      case GREEN:
        return "green";
      case BLUE:
        return "blue";
      default:
        return "unknown color";
    }
  }
  COLOR mColor;
};




class Rectangle : public AbstractShape {
  public:
  Rectangle(AbstractShape::COLOR color): AbstractShape(color){}
  void draw() const override {
    std::cout << "Drawing " << asString(mColor) << " rectangle\n";
  }
};

class Square : public AbstractShape {
  public:
  Square(AbstractShape::COLOR color): AbstractShape(color){}
  void draw() const override {
    std::cout << "Drawing " << asString(mColor) << " square\n";
  }
};

class Circle : public AbstractShape {
  public:
  Circle(AbstractShape::COLOR color): AbstractShape(color){}
  void draw() const override {
    std::cout << "Drawing " << asString(mColor) << " circle\n";
  }
};

// using the template method pattern here, as the actual
// behaviour of 'getShape' will be defined via specialization
// of virtual method getColor through subclassing
class AbstractShapeFactory {
  public:
  ~AbstractShapeFactory(){}
  virtual AbstractShape::COLOR getColor() const = 0;
  virtual std::shared_ptr<IShape> getShape(std::string shapeType){ 
     if(shapeType.empty()){
      return nullptr;
    }
    if(boost::iequals(shapeType,"CIRCLE")){
        return std::shared_ptr<IShape>(new Circle(getColor()));
    } else if(boost::iequals(shapeType,"RECTANGLE")){
        return std::shared_ptr<IShape>(new Rectangle(getColor()));
    } else if(boost::iequals(shapeType,"SQUARE")){
        return std::shared_ptr<IShape>(new Square(getColor()));
    }  

    return nullptr;
  }
};

// However the benefit of subclassing over maintaining
// 'mColor' state in base class is not that clear in this simple case
// It is propably beneficial when the distinction between various
// families of widgets (IShape) goes well beyond color difference.
class RedShapeFactory : public AbstractShapeFactory {
  public:
    AbstractShape::COLOR getColor() const override {
      return AbstractShape::COLOR::RED;}
};

class GreenShapeFactory : public AbstractShapeFactory {
  public:
    AbstractShape::COLOR getColor() const override {
      return AbstractShape::COLOR::GREEN;}
};

class BlueShapeFactory : public AbstractShapeFactory {
  public:
    AbstractShape::COLOR getColor() const override {
      return AbstractShape::COLOR::BLUE;}
};

// Factory of factories. The Abstract Factory design pattern is a case
// of Factory design pattern applied to various factory types.
class FactoryProducer {
  public:
    std::shared_ptr<AbstractShapeFactory> getFactory(std::string factoryType){
      if(factoryType.empty()){
        return nullptr;
      }

      if(boost::iequals(factoryType,"RED")){
        return std::shared_ptr<AbstractShapeFactory>(new RedShapeFactory());
      } else if(boost::iequals(factoryType,"GREEN")){
        return std::shared_ptr<AbstractShapeFactory>(new GreenShapeFactory());
      } else if(boost::iequals(factoryType,"BLUE")){
        return std::shared_ptr<AbstractShapeFactory>(new BlueShapeFactory());
      }
      return nullptr;
    }
};


int main(int argc, char* argv[]){

  FactoryProducer producer;

  // producing set of red widgets
  std::shared_ptr<AbstractShapeFactory> redFactory = producer.getFactory("Red");
  std::shared_ptr<IShape> shape1 = redFactory->getShape("CIRCLE");
  shape1->draw();
  std::shared_ptr<IShape> shape2 = redFactory->getShape("RECTANGLE");
  shape2->draw();
  std::shared_ptr<IShape> shape3 = redFactory->getShape("SQUARE");
  shape3->draw();

  // producing set of green widgets
  std::shared_ptr<AbstractShapeFactory> greenFactory=producer.getFactory("Green");
  std::shared_ptr<IShape> shape4 = greenFactory->getShape("CIRCLE");
  shape4->draw();
  std::shared_ptr<IShape> shape5 = greenFactory->getShape("RECTANGLE");
  shape5->draw();
  std::shared_ptr<IShape> shape6 = greenFactory->getShape("SQUARE");
  shape6->draw();

  // producing set of red widgets
  std::shared_ptr<AbstractShapeFactory> blueFactory = producer.getFactory("Blue");
  std::shared_ptr<IShape> shape7 = blueFactory->getShape("CIRCLE");
  shape7->draw();
  std::shared_ptr<IShape> shape8 = blueFactory->getShape("RECTANGLE");
  shape8->draw();
  std::shared_ptr<IShape> shape9 = blueFactory->getShape("SQUARE");
  shape9->draw();

  return 0;
}

