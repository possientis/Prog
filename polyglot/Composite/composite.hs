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

data Expression           = Leaf ExpressionLeaf | Composite ExpressionComposite
data ExpressionLeaf       = ExpInt Int | Mult | PLus
data ExpressionComposite  = Nil | Cons Expression ExpressionComposite

class IExpression a where
  eval    :: a -> Environment -> Expression
  apply   :: a -> ExpressionComposite -> Expression
  show    :: a -> String
  isList  :: a -> Bool
  isInt   :: a -> Bool
  
  
isNil :: ExpressionComposite -> Bool
isNil (Cons _ _) = False
isNil _          = True

foldLeft  :: ExpressionComposite -> b -> (b -> Expression -> b) -> b
foldLeft list init oper = fold list init where
  fold Nil acc = acc
  fold (Cons car cdr) acc = fold cdr (oper acc car)



foldRight :: ExpressionComposite -> b -> (Expression -> b -> b) -> b
foldRight Nil            init _    = init
foldRight (Cons car cdr) init oper = oper car (foldRight cdr init oper)


--evalList  :: ExpressionComposite -> Environment -> ExpressionComposite



