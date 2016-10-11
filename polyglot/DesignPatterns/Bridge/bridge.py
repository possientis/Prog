# Bridge design pattern

# bridge implementation interface
class DrawAPI(object):
    def drawCircle(self, radius, x, y):
        raise Exception("DrawAPI::drawCircle is not implemented")

# concrete bridge implementation classes implementing DrawAPI interface
class RedCircle(DrawAPI):
    def drawCircle(self, radius, x, y):
        print("Drawing Circle[ color: red  , radius: " + str(radius) 
                + ", x: " + str(x) + ", y: " + str(y) + "]")

class GreenCircle(DrawAPI):
    def drawCircle(self, radius, x, y):
        print("Drawing Circle[ color: green, radius: " + str(radius) 
                + ", x: " + str(x) + ", y: " + str(y) + "]")

# create an abstract class Shape using the DrawAPI interface.
class Shape:
    def __init__(self,drawAPI):
        self._drawAPI = drawAPI
    def draw(self):
        raise Exception("Shape::draw is not implemented")

# create concrete class implementing the Shape interface (abstract class)
class Circle(Shape):
    def __init__(self, x, y, radius, drawAPI):
        Shape.__init__(self,drawAPI)
        self._x = x
        self._y = y
        self._radius = radius
    def draw(self):
        self._drawAPI.drawCircle(self._radius, self._x, self._y)

# Use Shape and DrawAPI classes to draw different colored circles
# implementation of concrete circles selected at run time.
redCircle = Circle(100, 100, 10, RedCircle())
greenCircle = Circle(100, 100, 10, GreenCircle())
redCircle.draw()
greenCircle.draw()


