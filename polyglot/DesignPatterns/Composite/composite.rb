# Composite Design Pattern

# The composite design pattern consists in creating an abstract class
# or interface 'Component' which allows client code to handle certain 
# types of primitive objects of type 'Leaf' and various combinations
# thereof in a uniform way. These combinations can be of various nature
# and are unified in a common type 'Composite', where both 'Leaf' and 
# 'Composite' are subclasses of 'Component'.
#
# There are many examples where the composite pattern is applicable
# e.g. the DOM for html and abstract syntax trees for formal languages, 
# inductive data types of Haskell and Coq, etc.
#
# In the SICP course at MIT, a key idea relating to properties of
# programming languages is the existence of 'primitive objects' (Leaf)
# and 'means of combination', allowing the creation of new objects
# (Composite) while remaining within the language. The Composite 
# patterns allows us to regard every language entity as a 'Component' 
# which can be combined with other 'Component'(either 'Leaf' or 
# 'Composite') to obtain a new Component. In Lisp we could say that 
# every Component (which we shall call 'Expression') is either a Leaf 
# (which we shall call 'ExpressionLeaf') or a list of expressions 
# (which we shall call 'ExpressionComposite'). The means of combinations 
# in this case are are simply reduced to gathering objects within lists:
#
# Expression          := ExpressionLeaf | ExpressionComposite
# ExpressionComposite := Nil | Cons Expression ExpressionComposite
#

class Environment
end

class AssertionError < RuntimeError
end
def assert(condition)
  if !condition then
    raise AssertionError
  end
end

#******************************************************************************#
#*                            class Expression                                *#
#******************************************************************************#
#
class Expression
  def eval(env)
    raise NotImplementedError.new "Expression::eval is not implemented"
  end
  def apply(args)
    raise NotImplementedError.new "Expression::apply is not implemented"
  end
  def to_s()
    raise NotImplementedError.new "Expression::toString is not implemented"
  end
  def isList()
    raise NotImplementedError.new "Expression::isList is not implemented"
  end
  def isInt() return false end 
end

#******************************************************************************#
#*                            class ExpressionLeaf                            *#
#******************************************************************************#
#
class ExpressionLeaf < Expression
  def isList() return false end
end 


#******************************************************************************#
#*                         class ExpressionComposite                          *#
#******************************************************************************#

class ExpressionComposite < Expression
  def isList() return true end
  def isNil()
    raise NotImplementedError.new "ExpressionComposite::isNil is not implemented"
  end
  def foldLeft(init, operator)
    out = init
    _next = self;
    while !_next.isNil do
      assert(_next.is_a?(Cons))
      cell = _next  # would be downcasting in other languages
      out = operator.call(out,cell.head())
      _next = cell.tail
    end
    return out
  end
  def foldRight(init, operator)
    if isNil() then return init end
    assert(self.is_a?(Cons))
    cell = self   # would be downcasting in other languages
    # implementation not stack friendly. May need to be changed
    return operator.call(cell.head, cell.tail.foldRight(init, operator))
  end

  # This does not evaluate the expression, but rather returns
  # the list (itself an ExpressionComposite) of values (each 
  # value is itself an expression, albeit often of simpler type) 
  # obtained by evaluating each expression within the list
  def evalList(env)
    return foldRight(Nil.new, lambda {|exp,list| Cons.new(exp.eval(env),list)})
  end
end
    
#******************************************************************************#
#*                              class Nil                                     *#
#******************************************************************************#
class Nil < ExpressionComposite
  def isNil() return true end
  def eval(env) return self end
  def apply(list)
    raise NoMethodError.new "Nil is not an operator"
  end
  def to_s() return "Nil" end
end


#******************************************************************************#
#*                              class Cons                                    *#
#******************************************************************************#

class Cons < ExpressionComposite
  def initialize(car, cdr)
    @car = car  # car, head, first
    @cdr = cdr  # cdr, tail, rest
  end
  attr_reader :head, :tail
  def head() return @car end
  def tail() return @cdr end
  def eval(env)
    values = evalList(env)
    assert(values.is_a?(Cons))
    operator  = values.head
    arguments = values.tail
    return operator.apply(arguments)
  end
  def apply(args)
    raise NoMethodError.new "Lambda expression are not yet supported"
  end
  def isNil() return false end
  def to_s()
    return foldLeft("(",lambda {|str,exp| str + exp.to_s + " "}) + "\b)"
  end
end

#******************************************************************************#
#*                              class ExpInt                                  *#
#******************************************************************************#

class ExpInt < ExpressionLeaf
  attr_reader :toInt  # property getter is automatically defined
  def initialize(value) @toInt = value end
  def eval(env) return self end # self-evaluating
  def apply(args)
    raise NoMethodError.new "An integer is not an operator"
  end
  def to_s() return @toInt.to_s() end
  def isInt() return true end
end

#******************************************************************************#
#*                              class Primitive                               *#
#******************************************************************************#

class Primitive < ExpressionLeaf 
end

#******************************************************************************#
#*                              class Plus                                    *#
#******************************************************************************#

class Plus < Primitive
  def eval(env) return self end 
  def apply(args)
    sum = args.foldLeft(0, lambda {|res, exp|
      if exp.isInt then
        return res + exp.toInt
      else
        raise ArgumentError.new "+: argument is not a valid integer"
      end
    })
    return ExpInt.new(sum)
  end
  def to_s() return "+" end
end

#******************************************************************************#
#*                              class Mult                                    *#
#******************************************************************************#

class Mult < Primitive
  def eval(env) return self end 
  def apply(args)
    prod = args.foldLeft(1, lambda {|res, exp|
      if exp.isInt then
        return res * exp.toInt
      else
        raise ArgumentError.new "*: argument is not a valid integer"
      end
    })
    return ExpInt.new(prod)
  end
  def to_s() return "*" end
end

#******************************************************************************#
#*                                     Main                                   *#
#******************************************************************************#

env   = Environment.new
two   = ExpInt.new(2)
seven = ExpInt.new(7)
five  = ExpInt.new(5)
plus  = Plus.new
mult  = Mult.new
exp1  = Cons.new( # (+ 2 7 5)
             plus,
             Cons.new(
                  two,
                  Cons.new(
                       seven,
                       Cons.new(
                            five,
                            Nil.new))))
exp2  = Cons.new( # (*2 (+ 2 7 5) 5)
             mult,
             Cons.new(
                  two,
                  Cons.new(
                       exp1,
                       Cons.new(
                            five,
                            Nil.new))))

print "The evaluation of the Lisp expression: #{exp2}\n"
print "yields the value: #{exp2.eval(env)}\n"











