// Bridge design pattern
#include <iostream>
#include <memory>

// bridge implementation interface
class DrawAPI {
  public:
    virtual ~DrawAPI(){}
    virtual void drawCircle(int radius, int x, int y) const = 0;
};

// concrete bridge implementation classes implementing DrawAPI interface
class RedCircle : public DrawAPI {
  public:
    virtual ~RedCircle(){}
    void drawCircle(int radius, int x, int y) const override {
      std::cout << "Drawing Circle[ color: red  , radius: " 
        << radius << ", x: " << x << ", y: " << y << "]\n";
  }
};

class GreenCircle : public DrawAPI {
  public:
    virtual ~GreenCircle(){}
    void drawCircle(int radius, int x, int y) const override {
      std::cout << "Drawing Circle[ color: green, radius: " 
        << radius << ", x: " << x << ", y: " << y << "]\n";
  }
};

// create an abstract class Shape using the DrawAPI interface.
class Shape {
  protected:
    std::shared_ptr<DrawAPI> drawAPI;
    Shape(DrawAPI* drawAPI) : drawAPI(drawAPI){}
  public:
    virtual ~Shape(){}
    virtual void draw() const = 0;// abstraction need not follow implementation API
};

// create concrete class implementing the Shape interface (abstract class)
class Circle : public Shape {
  private:
    int x, y, radius;
  public:
    ~Circle(){}
    Circle(int x, int y, int radius, DrawAPI* drawAPI) : Shape(drawAPI){
    this->x = x;
    this->y = y;
    this->radius = radius;
  }
    void draw() const override {
    drawAPI->drawCircle(radius,x,y);
  }
};


// Use Shape and DrawAPI classes to draw different colored circles
int main(int argc, char* argv[], char* envp[]){
  // implementation of concrete circles selected at run time.
  typedef std::shared_ptr<Shape> ShapePtr;
  ShapePtr redCircle = ShapePtr(new Circle(100, 100, 10, new RedCircle()));
  ShapePtr greenCircle = ShapePtr(new Circle(100, 100, 10, new GreenCircle()));
  redCircle->draw();
  greenCircle->draw();
  return 0;
}

