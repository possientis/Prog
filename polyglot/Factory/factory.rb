# Factory design pattern

class Shape
  def draw
    raise Exception.new "Shape::draw is not implemented"
  end
end

class Rectangle < Shape
  def draw
    puts "Inside Rectangle::draw() method."
  end
end

class Square < Shape
  def draw
    puts "Inside Square::draw() method."
  end
end

class Circle < Shape
  def draw
    puts "Inside Circle::draw() method."
  end
end

class ShapeFactory
  # use getShape method to get object of type Shape
  def getShape shapeType
    if shapeType.empty? then return nil end

    if shapeType.casecmp("CIRCLE") == 0
      return Circle.new
    elsif shapeType.casecmp("RECTANGLE") == 0 
      return Rectangle.new
    elsif shapeType.casecmp("SQUARE") == 0
      return Square.new
    end

    return nil
  end
end

shapeFactory = ShapeFactory.new

#get an object of type Circle and call its draw method
shape1 = shapeFactory.getShape("CIRCLE")
shape1.draw

#get an object of type Rectangle and call its draw method
shape2 = shapeFactory.getShape("RECTANGLE")
shape2.draw

#get an object of type Square and call its draw method
shape3 = shapeFactory.getShape("SQUARE")
shape3.draw


