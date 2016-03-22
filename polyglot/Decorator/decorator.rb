# Decorator Design Pattern

# The implementation of the decorator pattern in ruby does not follow
# the pattern encountered in other languages, due to ruby built in module mixins

class Pizza
  def description()
    raise NotImplementedError.new "Pizza::description is not implemented"
  end 

  def cost()
    raise NotImplementedError.new "Pizza::cost is not implemented"
  end
end

class PlainPizza < Pizza
  def description() return "Plain Pizza" end
  def cost() return 3.0 end
end

module WithExtraCheese
  def description()
    return super  +  " + extra cheese"
  end
  def cost()
    return super + 0.5
  end
end

module WithExtraOlives
  def description()
    return super  +  " + extra olives"
  end
  def cost()
    return super + 0.7
  end
end

module WithExtraAnchovies
  def description()
    return super  +  " + extra anchovies"
  end
  def cost()
    return super + 0.8
  end
end

class NicePizza < PlainPizza
  include WithExtraCheese
end

class SuperPizza < NicePizza
  include WithExtraOlives
end

class UltraPizza < SuperPizza
  include WithExtraAnchovies
end


plainPizza  = PlainPizza.new
nicePizza   = NicePizza.new
superPizza  = SuperPizza.new
ultraPizza  = UltraPizza.new

puts  "Plain Pizza: "   +
      "\tCost: "        + plainPizza.cost.to_s +
      "\tDescription: " + plainPizza.description  

puts  "Nice Pizza: "    +
      "\tCost: "        + nicePizza.cost.to_s +
      "\tDescription: " + nicePizza.description  

puts  "Super Pizza: "   +
      "\tCost: "        + superPizza.cost.to_s +
      "\tDescription: " + superPizza.description  

puts  "Ultra Pizza: "   +
      "\tCost: "        + ultraPizza.cost.to_s +
      "\tDescription: " + ultraPizza.description  



