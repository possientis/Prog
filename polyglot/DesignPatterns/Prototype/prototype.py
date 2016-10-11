# Prototype design pattern
# Imagine that in order to instantiate certain objects we need to carry out
# expensive database queries. In order to improve performance, it would 
# be beneficial to cache whatever object is created from the database
# and return a copy of the cached object whenever a subsequent request
# for object instantiation arises.

class Cloneable:
    def clone(self):
        raise Exception("Cloneable::clone is not implemented")

class Shape(Cloneable):
    def __init__(self):
        self.ID = None
    def draw(self):
        raise Exception("Shape::draw is not implemented")
    def clone(self):
        raise Exception("Shape::clone is not implemented")

class Rectangle(Shape):
    def draw(self):
        print("Inside Rectangle::draw() method.")
    def clone(self):
        clone = Rectangle()
        clone.ID = self.ID
        return clone

class Square(Shape):
    def draw(self):
        print("Inside Square::draw() method.")
    def clone(self):
        clone = Square()
        clone.ID = self.ID
        return clone

class Circle(Shape):
    def draw(self):
        print("Inside Circle::draw() method.")
    def clone(self):
        clone = Circle()
        clone.ID = self.ID
        return clone

class PrototypeManager:
    def __init__(self):
        self.shapeMap = {}   #empty dictionary
    def getShape(self,shapeId):
        cachedShape = self.shapeMap[shapeId]
        return cachedShape.clone()
    def loadCache(self):
        rect = Rectangle()
        rect.ID = "1"
        self.shapeMap[rect.ID] = rect

        square = Square()
        square.ID = "2"
        self.shapeMap[square.ID] = square

        circle = Circle()
        circle.ID = "3"
        self.shapeMap[circle.ID] = circle

# need a prototype manager
manager = PrototypeManager()
# prototype manager registers a few prototypes
manager.loadCache()
# prototype manager can now be used as factory object
clonedShape1 = manager.getShape("1")
clonedShape1.draw()

clonedShape2 = manager.getShape("2")
clonedShape2.draw()

clonedShape3 = manager.getShape("3")
clonedShape3.draw()


