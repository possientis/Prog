# Singleton design pattern

class SingleObject
  @@instance = SingleObject.new

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
if object1 == object2                 # ==, eql?, equal? all the same in Object
  puts "The two objects are the same"
end
