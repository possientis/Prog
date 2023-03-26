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
class AbstractShapeFactory(metaclass=ABCMeta):
    @abstractmethod
    def getColor(self):
        return NotImplemented
    
    def getShape(self, shapeType):
        if not shapeType:   # testing for empty string
            return None
        if shapeType.upper() == "CIRCLE":
            return Circle(self.getColor())
        elif shapeType.upper() == "RECTANGLE":
            return Rectangle(self.getColor())
        elif shapeType.upper() == "SQUARE":
            return Square(self.getColor())
        return None

# However the benefit of subclassing over maintaining
# 'mColor' state in base class is not that clear in this simple case
# It is propably beneficial when the distinction between various
# families of widgets (IShape) goes well beyond color difference.
class RedShapeFactory(AbstractShapeFactory):
    def getColor(self):
        return AbstractShape.COLOR.RED

class GreenShapeFactory(AbstractShapeFactory):
    def getColor(self):
        return AbstractShape.COLOR.GREEN

class BlueShapeFactory(AbstractShapeFactory):
    def getColor(self):
        return AbstractShape.COLOR.BLUE

# Factory of factories. The Abstract Factory design pattern is a case
# of Factory design pattern applied to various factory types.
class FactoryProducer:
    def getFactory(self,factoryType):
        if not factoryType:     # testing for empty string
            return None
        if factoryType.upper() == "RED":
            return RedShapeFactory()
        elif factoryType.upper() == "GREEN":
            return GreenShapeFactory()
        elif factoryType.upper() == "BLUE":
            return BlueShapeFactory()
        return None


producer = FactoryProducer()
# producing set of red widgets
redFactory = producer.getFactory("Red")
shape1 = redFactory.getShape("CIRCLE")
shape2 = redFactory.getShape("RECTANGLE")
shape3 = redFactory.getShape("SQUARE")
shape1.draw()
shape2.draw()
shape3.draw()

# producing set of green widgets
greenFactory = producer.getFactory("Green")
shape4 = greenFactory.getShape("CIRCLE")
shape5 = greenFactory.getShape("RECTANGLE")
shape6 = greenFactory.getShape("SQUARE")
shape4.draw()
shape5.draw()
shape6.draw()

# producing set of blue widgets
blueFactory = producer.getFactory("Blue")
shape7 = blueFactory.getShape("CIRCLE")
shape8 = blueFactory.getShape("RECTANGLE")
shape9 = blueFactory.getShape("SQUARE")
shape7.draw()
shape8.draw()
shape9.draw()

