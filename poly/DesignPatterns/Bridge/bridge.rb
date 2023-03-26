# Bridge design pattern

# bridge implementation interface
class DrawAPI
  def drawCircle(radius, x, y)
    raise Exception.new "DrawAPI::drawCircle is not implemented"
  end
end

# concrete bridge implementation classes implementing DrawAPI interface
class RedCircle < DrawAPI
  def drawCircle(radius, x, y)
    puts "Drawing Circle[ color: red  , radius: #{radius}, x: #{x}, y: #{y}]"
  end
end

class GreenCircle < DrawAPI
  def drawCircle(radius, x, y)
    puts "Drawing Circle[ color: green, radius: #{radius}, x: #{x}, y: #{y}]"
  end
end

# create an abstract class Shape using the DrawAPI interface.
class Shape
  def initialize(drawAPI)
    @drawAPI = drawAPI
  end
  def draw  # abstraction need not follow implementation API
    raise Exception.new "Shape::draw is not implemented"
  end
end


# create concrete class implementing the Shape interface (abstract class)
class Circle < Shape
  def initialize(x, y, radius, drawAPI)
    super drawAPI
    @x = x
    @y = y
    @radius = radius
  end
  def draw
    @drawAPI.drawCircle(@radius,@x,@y)
  end
end


# Use Shape and DrawAPI classes to draw different colored circles
# implementation of concrete circles selected at run time.

redCircle = Circle.new 100, 100, 10, RedCircle.new
greenCircle = Circle.new 100, 100, 10, GreenCircle.new
redCircle.draw
greenCircle.draw




