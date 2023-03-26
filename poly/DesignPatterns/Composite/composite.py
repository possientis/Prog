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

class Environment(object):
    pass

#******************************************************************************#
#*                            class Expression                                *#
#******************************************************************************#

class Expression(object):
    def eval(self, env):
        raise NotImplementedError("Expression::eval is not implemented") 
    def apply(self, args):
        raise NotImplementedError("Expression::apply is not implemented")
    def __repr__(self):
        raise NotImplementedError("Expression::__repr__ is not implemented")
    @property
    def isList(self):
        raise NotImplementedError("Expression::isList is not implemented")
    @property
    def isInt(self): return False


#******************************************************************************#
#*                          class ExpressionLeaf                              *#
#******************************************************************************#

class ExpressionLeaf(Expression):
    @property
    def isList(self): return False


#******************************************************************************#
#*                        class ExpressionComposite                           *#
#******************************************************************************#

class ExpressionComposite(Expression):
    @property
    def isList(self): return True
    @property
    def isNil(self):
        raise NotImplementedError("ExpressionComposite::isNil is not implemented")
    def foldLeft(self, init, operator):
        out = init
        _next = self
        while not _next.isNil:
            assert(isinstance(_next, Cons))
            cell = _next    # would downcast in other languages
            out = operator(out, cell.head)
            _next = cell.tail
        return out
    def foldRight(self, init, operator):
        if self.isNil : return init
        assert(isinstance(self, Cons))
        cell = self         # would downcast in other languages
        # implementation not stack friendly. May need to change
        return operator(cell.head, cell.tail.foldRight(init, operator))
    # This does not evaluate the expression, but rather returns
    # the list (itself an ExpressionComposite) of values (each 
    # value is itself an expression, albeit often of simpler type) 
    # obtained by evaluating each expression within the list
    def evalList(self, env):
        def operator(exp, args): return Cons(exp.eval(env), args)
        return self.foldRight(Nil(), operator)

 
#******************************************************************************#
#*                                  class Nil                                 *#
#******************************************************************************#
    
class Nil(ExpressionComposite):
    @property
    def isNil(self): return True
    def eval(self, env): return self    # self-evaluating
    def apply(self, args):
        raise NotImplementedError("Nil is not an operator") 
    def __repr__(self): return "Nil"


#******************************************************************************#
#*                                  class Cons                                *#
#******************************************************************************#

class Cons(ExpressionComposite):
    def __init__(self, car, cdr):
        self.car = car  # car, head, first
        self.cdr = cdr  # cdr, tail, rest
    @property
    def head(self): return self.car
    @property
    def tail(self): return self.cdr
    def eval(self, env):
        values = self.evalList(env)
        assert(isinstance(values, Cons))
        operator    = values.head
        arguments   = values.tail
        return operator.apply(arguments)
    def apply(self, args):
        raise NotImplementedError("Lambda expression are not yet supported")
    @property
    def isNil(self): return False
    def __repr__(self):
        def concat(res,exp): return res + str(exp) + " "
        return self.foldLeft("(",concat) + "\b)"


#******************************************************************************#
#*                                  class ExpInt                              *#
#******************************************************************************#

class ExpInt(ExpressionLeaf):
    def __init__(self, value):
        self._value = value
    @property
    def toInt(self): return self._value
    def eval(self, env): return self    # self-evaluating
    def apply(self, args):
        raise NotImplementedError("An integer is not an operator")
    def __repr__(self): return str(self._value)
    @property
    def isInt(self): return True


#******************************************************************************#
#*                                  class Primitive                           *#
#******************************************************************************#

class Primitive(ExpressionLeaf): pass


#******************************************************************************#
#*                                  class Plus                                *#
#******************************************************************************#

class Plus(Primitive):
    def eval(self, env): return self
    def apply(self, args):
        def operator(res, exp):
            if exp.isInt:
                return res + exp.toInt
            else:
                raise TypeError("+: argument is not a valid integer")
        _sum = args.foldLeft(0, operator)
        return ExpInt(_sum)
    def __repr__(self): return "+"

#******************************************************************************#
#*                                  class Mult                                *#
#******************************************************************************#

class Mult(Primitive):
    def eval(self, env): return self
    def apply(self, args):
        def operator(res, exp):
            if exp.isInt:
                return res * exp.toInt
            else:
                raise TypeError("*: argument is not a valid integer")
        prod = args.foldLeft(1, operator)
        return ExpInt(prod)
    def __repr__(self): return "*"

env     = Environment()
two     = ExpInt(2)
seven   = ExpInt(7)
five    = ExpInt(5)
plus    = Plus()
mult    = Mult()
exp1    = Cons(plus, Cons(two, Cons(seven, Cons(five, Nil())))) # (+ 2 7 5)
exp2    = Cons(mult, Cons(two, Cons(exp1, Cons(five, Nil()))))

print("The evaluation of the Lisp expression: " + str(exp2))
print("yields the value: " + str(exp2.eval(env)))


                


                







