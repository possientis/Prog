# Prototype design pattern
# Imagine that in order to instantiate certain objects we need to carry out
# expensive database queries. In order to improve performance, it would 
# be beneficial to cache whatever object is created from the database
# and return a copy of the cached object whenever a subsequent request
# for object instantiation arises.

class Cloneable
  def clone
    raise Exception.new "Cloneable::clone is not implemented"
  end
end

class Shape < Cloneable
  attr_reader :id
  attr_writer :id

  def initialize
    @id = nil
  end
  def draw
    raise Exception.new "Shape::draw is not implemented"
  end
  def clone
    raise Excaption.new "Shape::clone is not implemented"
  end
end

class Rectangle < Shape
  def draw
    puts "Inside Rectangle::draw() method."
  end
  def clone
    clone = Rectangle.new
    clone.id = @id
    return clone
  end
end

class Square < Shape
  def draw
    puts "Inside Square::draw() method."
  end
  def clone
    clone = Square.new
    clone.id = @id
    return clone
  end
end

class Circle < Shape
  def draw
    puts "Inside Circle::draw() method."
  end
  def clone
    clone = Circle.new
    clone.id = @id
    return clone
  end
end

class PrototypeManager
  def initialize
    @shapeMap = {}
  end
  def getShape(shapeId)
    cachedShape = @shapeMap[shapeId]
    return cachedShape.clone
  end
  def loadCache
    rect = Rectangle.new
    rect.id = "1"
    @shapeMap["1"] = rect

    square = Square.new
    square.id = "2"
    @shapeMap["2"] = square

    circle = Circle.new
    circle.id = "3"
    @shapeMap["3"] = circle
  end
end

# need a prototype manager
manager = PrototypeManager.new
# prototype manager registers a few prototypes
manager.loadCache
# prototype manager can now be used as factory object
clonedShape1 = manager.getShape("1")
clonedShape1.draw

clonedShape2 = manager.getShape("2")
clonedShape2.draw

clonedShape3 = manager.getShape("3")
clonedShape3.draw










