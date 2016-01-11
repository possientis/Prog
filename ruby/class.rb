class Person
  attr_reader :name, :age
  def initialize(name,age)
    @name,@age = name, age
  end
  
  def <=>(person) # comparison operator
    age <=> person.age
  end

  def to_s
    "#{name}(#{age})"
  end
end


group = [
  Person.new("Bob", 33),
  Person.new("Chris", 16),
  Person.new("Ash", 23)
]

puts group.sort.reverse

class Time  # re-open Ruby's Time class
  def yesterday
    self - 86400
  end
end

today = Time.now
# does not work ??
#yesterday = Time.yesterday

class Being
  def initialize name="unknown", age = 0
    @name = name
    @age = age
  end
  def get_name
    @name
  end
  def to_s
    "Name: #{@name}, Age: #{@age}"
  end
end

b1 = Being.new "jane"
b2 = Being.new "beky"
b3 = Being.allocate # constructor not called

puts b1.get_name
puts b2.get_name
puts b3
puts b1
puts b2

puts b1.send :get_name

class Circle
  def self.info
    puts "This is a static method"
  end

  PI = 3.14159
  def initialize radius
    @radius = radius
  end
  def area
    @radius*@radius*PI
  end
end

c0 = Circle.new(1.0)
puts c0.area

c1 = Circle.new(2.0)
puts c1.area

Circle.info

class Some
  def method1
    puts "public method1 called"
  end

  public
  def method2
    puts "public method2 called"
  end

  def method3
    puts "public method3 called"
    method1
    self.method1
  end
end

s = Some.new
s.method1
s.method2
s.method3


class Some2
  def initialize
    method1
    # self.method1
  end

  private
  def method1
    puts "private method1 called"
  end
end

s = Some2.new
# s.method1 # wont work
#
#
p [1,2,3,4] # p stands for print it seems

p Being.ancestors

class Wood
  def self.info
    "This is a Wood class" 
  end
end

class Brick
  class << self
    def info
      "This is a Brick class" 
    end
  end
end

class Rock
       
end

def Rock.info
     "This is a Rock class" 
end


p Wood.info
p Brick.info
p Rock.info
  



