-- Composite Design Pattern

-- The composite design pattern consists in creating an abstract class
-- or interface 'Component' which allows client code to handle certain 
-- types of primitive objects of type 'Leaf' and various combinations
-- thereof in a uniform way. These combinations can be of various nature
-- and are unified in a common type 'Composite', where both 'Leaf' and 
-- 'Composite' are subclasses of 'Component'.
--
-- There are many examples where the composite pattern is applicable
-- e.g. the DOM for html and abstract syntax trees for formal languages, 
-- inductive data types of Haskell and Coq, etc.
--
-- In the SICP course at MIT, a key idea relating to properties of
-- programming languages is the existence of 'primitive objects' (Leaf)
-- and 'means of combination', allowing the creation of new objects
-- (Composite) while remaining within the language. The Composite 
-- patterns allows us to regard every language entity as a 'Component' 
-- which can be combined with other 'Component'(either 'Leaf' or 
-- 'Composite') to obtain a new Component. In Lisp we could say that 
-- every Component (which we shall call 'Expression') is either a Leaf 
-- (which we shall call 'ExpressionLeaf') or a list of expressions 
-- (which we shall call 'ExpressionComposite'). The means of combinations 
-- in this case are are simply reduced to gathering objects within lists:
--
-- Expression          := ExpressionLeaf | ExpressionComposite
-- ExpressionComposite := Nil | Cons Expression ExpressionComposite
--

data Environment = Environment
data Expression = Leaf ExpressionLeaf | List ExpressionComposite
data ExpressionComposite = Comp Nil | MkCons Cons 
data ExpressionLeaf = Oper Primitive | Value ExpInt
data Primitive = MkPlus Plus | MkMult Mult

class IExpression a where
  embed   :: a -> Expression
  isList  :: a -> Bool
  isInt   :: a -> Bool
  isNil   :: a -> Bool
  eval    :: a -> Environment -> Expression
  apply   :: a -> ExpressionComposite -> Expression
  

data Nil = Nil
instance Show Nil where show Nil = "Nil"
instance IExpression Nil where
  embed   _       = List (Comp Nil)
  isList  _       = True
  isInt   _       = False
  isNil   _       = True
  eval    _ _     = embed Nil
  apply   _ _     = error "Nil is not an operator"

data ExpInt = ExpInt Int
instance Show ExpInt where show (ExpInt n) = (show n)
instance IExpression ExpInt where
  embed   int     = Leaf (Value int)
  isList  _       = False
  isInt   _       = True
  isNil   _       = error "isNil should be applied to composite expression only"
  eval    int _   = embed int
  apply   _   _   = error "An integer is not an operator"
  
data Plus = Plus
instance Show Plus where show Plus = "+"
instance IExpression Plus where
  embed   _       = Leaf (Oper (MkPlus Plus))
  isList  _       = False
  isInt   _       = False
  isNil   _       = error "isNil should be applied to composite expression only"
  eval    _   _   = embed Plus
  apply   _ args  = embed (ExpInt sum) where sum = 0 -- TBI 


data Mult = Mult
instance Show Mult where show Mult = "*"
instance IExpression Mult where
  embed   _       = Leaf (Oper (MkMult Mult))
  isList  _       = False
  isInt   _       = False
  isNil   _       = error "isNil should be applied to composite expression only"
  eval    _   _   = embed Mult
  apply   _ args  = embed (ExpInt sum) where sum = 0 -- TBI 

data Cons = Cons Expression ExpressionComposite
instance Show Cons where show (Cons car cdr) = "TBI"
instance IExpression Cons where
  embed   cons    = List (MkCons cons)
  isList  _       = True
  isInt   _       = False
  isNil   _       = False
  eval   (Cons car cdr) _ = embed (ExpInt 0) -- TBI 
  apply   _ _     = error "Lambda expression are not yet supported"







