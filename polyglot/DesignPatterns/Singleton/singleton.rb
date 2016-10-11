# Singleton design pattern

class SingleObject
  @@instance = SingleObject.new  # no infinite recursion?

  def self.getInstance
    return @@instance
  end

  def showMessage
    puts "The single object is alive and well"
  end

  private_class_method :new
end


object1 = SingleObject.getInstance
object1.showMessage

object2 = SingleObject.getInstance
if object1.equal?(object2)                 
  puts "The two objects are the same"
end

#The == comparison checks whether two values are equal
#eql? checks if two values are equal and of the same type
#equal? checks if two things are one and the same object.
#How do I remember which is which ... The longer the operator, 
#the more restrictive the test it performs
