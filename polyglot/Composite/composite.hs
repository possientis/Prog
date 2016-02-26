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
data ExpressionComposite  = Nil | Cons Expression ExpressionComposite
data ExpressionLeaf       = ExpInt Int | Mult | Plus
data Expression           = Leaf ExpressionLeaf | Composite ExpressionComposite

expInt :: Int -> Expression
expInt n = Leaf (ExpInt n)

plus :: Expression
plus = Leaf Plus

mult :: Expression
mult = Leaf Mult

class IExpression a where
  eval    :: a -> Environment -> Expression
  apply   :: a -> ExpressionComposite -> Expression
  isList  :: a -> Bool
  isInt   :: a -> Bool

instance IExpression Expression where
  -- isList
  isList (Leaf _)         = False
  isList (Composite _)    = True
  -- isInt
  isInt (Leaf (ExpInt _)) = True
  isInt _                 = False
  -- eval
  eval (Composite Nil) env = (Composite Nil)
  eval (Composite list) env = apply operator arguments where
    values = evalList list env
    (operator, arguments) = case values of
      Cons x y  -> (x,y)
      otherwise -> error "Should not happen"
  eval (Leaf (ExpInt x)) env  = Leaf (ExpInt x)  -- self-evaluating
  eval (Leaf Plus) env        = Leaf Plus        -- self-evaluating
  eval (Leaf Mult) env        = Leaf Mult        -- self-evaluating
  -- apply
  apply (Composite Nil) _     = error "Nil is not an operator"
  apply (Composite _) _       = error "Lambda expression are not yet supported"
  apply (Leaf (ExpInt _)) _   = error "An integer is not an operator"
  apply (Leaf Plus) args      = Leaf (ExpInt sum) where
    sum = foldLeft args 0 (\res -> \exp -> case exp of
      Leaf(ExpInt x) -> res + x
      otherwise      -> error "+: arguments is not a valid integer")
  apply (Leaf Mult) args      = Leaf (ExpInt prod) where
    prod = foldLeft args 1 (\res -> \exp -> case exp of
      Leaf(ExpInt x) -> res * x
      otherwise      -> error "*: arguments is not a valid integer")

instance Show Expression where
  show (Composite Nil) = "Nil"
  show (Composite list) = foldLeft list "(" (\str -> \exp -> 
    str ++ (show exp) ++ " ") ++ "\b)"
  show (Leaf (ExpInt x)) = show x
  show (Leaf Plus) = "+"
  show (Leaf Mult) = "*"


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

evalList  :: ExpressionComposite -> Environment -> ExpressionComposite
evalList list env = foldRight list Nil (\exp -> \args -> Cons (eval exp env) args)

head :: ExpressionComposite -> Expression
head (Cons exp _) = exp
head _ = error "head: illegal call"

tail :: ExpressionComposite -> ExpressionComposite
tail (Cons _ cdr) = cdr
tail _ = error "tail: illegal call" 

main = do 
  let
    env   = Environment
    two   = expInt 2
    seven = expInt 7
    five  = expInt 5
    exp1  = Composite (Cons plus (Cons two (Cons seven (Cons five Nil))))
    exp2  = Composite (Cons mult (Cons two (Cons exp1  (Cons five Nil))))
    in
    putStrLn ("The evaluation of the Lisp expression: " ++ (show exp2)) >>
    putStrLn ("yields the value: " ++ (show (eval exp2 env)))


