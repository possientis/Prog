# the Abstract Factory pattern looks like the factory pattern 
# applied to the production of various factories

class Shape
  def draw
    raise Exception.new "Shape::draw is not implemented"
  end
end

class AbstractShape < Shape
  def initialize
    @color = nil
  end
  def draw
    raise Exception.new "AbstractShape::draw is not implemented"
  end
  def self.asString(color)
    if color == :red
      return 'red'
    elsif color == :green
     return 'green'
    elsif color == :blue
     return 'blue'
    else
     return 'unknown color'
    end 
  end
end

class Rectangle < AbstractShape
  def initialize(color)
    @color = color
  end
  def draw
    puts "Drawing #{AbstractShape.asString(@color)} rectangle"
  end
end

class Square < AbstractShape
  def initialize(color)
    @color = color
  end
  def draw
    puts "Drawing #{AbstractShape.asString(@color)} square"
  end
end

class Circle < AbstractShape
  def initialize(color)
    @color = color
  end
  def draw
    puts "Drawing #{AbstractShape.asString(@color)} circle"
  end
end


# using the template method pattern here, as the actual
# behaviour of 'getShape' will be defined via specialization
# of virtual method getColor through subclassing

class AbstractShapeFactory
  def getColor
    raise Exception.new "AbstractShapeFactory::getColor is not implemented"
  end

  def getShape(shapeType)
    if shapeType.empty? then return nil end

    if shapeType.casecmp("CIRCLE") == 0
      return Circle.new(getColor)
    elsif shapeType.casecmp("RECTANGLE") == 0 
      return Rectangle.new(getColor)
    elsif shapeType.casecmp("SQUARE") == 0
      return Square.new(getColor)
    end

    return nil
  end

end

# However the benefit of subclassing over maintaining
# @color state in base class is not that clear in this simple case
# It is probably beneficial when the distinction between various
# families of widgets (Shape) goes well beyond color difference.

class RedShapeFactory < AbstractShapeFactory
  def getColor
    :red
  end
end

class GreenShapeFactory < AbstractShapeFactory
  def getColor
    :green
  end
end

class BlueShapeFactory < AbstractShapeFactory
  def getColor
    :blue
  end
end

# Factory of factories. The Abstract Factory design pattern is a case
# of Factory design pattern applied to various factory types.
class FactoryProducer
  def getFactory(factoryType)
    if factoryType.empty? then return nil end

    if factoryType.casecmp("RED") == 0
      return RedShapeFactory.new
    elsif factoryType.casecmp("GREEN") == 0
      return GreenShapeFactory.new
    elsif factoryType.casecmp("BLUE") == 0
      return BlueShapeFactory.new
    end

    return nil
  end
end

producer = FactoryProducer.new
# producing set of red widgets
redFactory = producer.getFactory("Red")
shape1 = redFactory.getShape("CIRCLE")
shape2 = redFactory.getShape("RECTANGLE")
shape3 = redFactory.getShape("SQUARE")
shape1.draw
shape2.draw
shape3.draw

# producing set of green widgets
greenFactory = producer.getFactory("Green")
shape4 = greenFactory.getShape("CIRCLE")
shape5 = greenFactory.getShape("RECTANGLE")
shape6 = greenFactory.getShape("SQUARE")
shape4.draw
shape5.draw
shape6.draw

# producing set of blue widgets
blueFactory = producer.getFactory("Blue")
shape7 = blueFactory.getShape("CIRCLE")
shape8 = blueFactory.getShape("RECTANGLE")
shape9 = blueFactory.getShape("SQUARE")
shape7.draw
shape8.draw
shape9.draw








