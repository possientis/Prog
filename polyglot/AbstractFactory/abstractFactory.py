# the Abstract Factory pattern looks like the factory pattern 
# applied to the production of various factories

from abc import ABCMeta
from abc import abstractmethod
from enum import Enum

class IShape(metaclass=ABCMeta):

    @abstractmethod
    def draw(self):
        return NotImplemented

class AbstractShape(IShape):
    @abstractmethod
    def draw(self):
        return NotImplemented
    COLOR = Enum('COLOR','RED GREEN BLUE')
    def asString(color):
        if color == AbstractShape.COLOR.RED:
            return 'red'
        elif color == AbstractShape.COLOR.GREEN:
            return 'green'
        elif color == AbstractShape.COLOR.BLUE:
            return 'blue'
        else:
            return 'unknown color'


class Rectangle(AbstractShape):
    def __init__(self,color):
        self.mColor = color
    def draw(self):
        print('Drawing ' + AbstractShape.asString(self.mColor) + ' rectangle')

class Square(AbstractShape):
    def __init__(self,color):
        self.mColor = color
    def draw(self):
        print('Drawing ' + AbstractShape.asString(self.mColor) + ' square')

class Circle(AbstractShape):
    def __init__(self,color):
        self.mColor = color
    def draw(self):
        print('Drawing ' + AbstractShape.asString(self.mColor) + ' circle')


# using the template method pattern here, as the actual
# behaviour of 'getShape' will be defined via specialization
# of virtual method getColor through subclassing

class ShapeFactory(object):
    # use getShape method to get object of type IShape
    def getShape(self, shapeType):

        if not shapeType:   # testing for empty string
            return None

        if shapeType.upper() == "CIRCLE":
            return Circle(AbstractShape.COLOR.RED)
        elif shapeType.upper() == "RECTANGLE":
            return Rectangle(AbstractShape.COLOR.RED)
        elif shapeType.upper() == "SQUARE":
            return Square(AbstractShape.COLOR.RED)

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

