from abc import ABCMeta
from abc import abstractmethod

class IShape(metaclass=ABCMeta):

    @abstractmethod
    def draw(self):
        return NotImplemented

class Rectangle(IShape):

    def draw(self):
        print("Inside Rectangle::draw() method.")

class Square(IShape):

    def draw(self):
        print("Inside Square::draw() method.")

class Circle(IShape):

    def draw(self):
        print("Inside Circle::draw() method.")


class ShapeFactory(object):
    # use getShape method to get object of type IShape
    def getShape(self, shapeType):

        if not shapeType:   # testing for empty string
            return None

        if shapeType.upper() == "CIRCLE":
            return Circle()
        elif shapeType.upper() == "RECTANGLE":
            return Rectangle()
        elif shapeType.upper() == "SQUARE":
            return Square()

        return None


shapeFactory = ShapeFactory()
# get an object of Circle and call its draw method
shape1 = shapeFactory.getShape("CIRCLE")
shape1.draw()

# get an object of Rectangle and call its draw method
shape2 = shapeFactory.getShape("RECTANGLE")
shape2.draw()

# get an object of Square and call its draw method
shape3 = shapeFactory.getShape("SQUARE")
shape3.draw()

