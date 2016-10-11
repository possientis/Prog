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

class IExpression a where
  upcast  :: a -> Expression
  isList  :: a -> Bool
  isInt   :: a -> Bool
  isNil   :: a -> Bool
  eval    :: a -> Environment -> Expression
  apply   :: a -> ExpressionComposite -> Expression
  

data Expression = Leaf ExpressionLeaf | List ExpressionComposite
instance Show Expression where
  show    (Leaf  x)   = show    x
  show    (List  x)   = show    x
instance IExpression Expression where
  upcast  (Leaf  x)   = upcast  x
  upcast  (List  x)   = upcast  x
  isList  (Leaf  x)   = isList  x
  isList  (List  x)   = isList  x
  isInt   (Leaf  x)   = isInt   x
  isInt   (List  x)   = isInt   x
  isNil   (Leaf  x)   = isNil   x
  isNil   (List  x)   = isNil   x
  eval    (Leaf  x)   = eval    x
  eval    (List  x)   = eval    x
  apply   (Leaf  x)   = apply   x  
  apply   (List  x)   = apply   x  

data ExpressionComposite = Comp Nil | MkCons Cons 
instance Show ExpressionComposite where
  show    (Comp   x)  = show    x
  show    (MkCons x)  = show    x
instance IExpression ExpressionComposite where
  upcast  (Comp   x)  = upcast  x
  upcast  (MkCons x)  = upcast  x
  isList  (Comp   x)  = isList  x
  isList  (MkCons x)  = isList  x
  isInt   (Comp   x)  = isInt   x
  isInt   (MkCons x)  = isInt   x
  isNil   (Comp   x)  = isNil   x
  isNil   (MkCons x)  = isNil   x
  eval    (Comp   x)  = eval    x
  eval    (MkCons x)  = eval    x
  apply   (Comp   x)  = apply   x
  apply   (MkCons x)  = apply   x

data Nil = Nil
instance Show Nil where 
  show      _         = "Nil"
instance IExpression Nil where
  upcast    _         = List (Comp Nil)
  isList    _         = True
  isInt     _         = False
  isNil     _         = True
  eval      _   _     = upcast Nil  -- self-evaluating
  apply     _   _     = error "Nil is not an operator"

data Cons = Cons Expression ExpressionComposite
instance Show Cons where
  show                = consShow  -- defined below
instance IExpression Cons where
  upcast    cons      = List (MkCons cons)
  isList    _         = True
  isInt     _         = False
  isNil     _         = False
  eval                = consEval  -- defined below
  apply     _   _     = error "Lambda expression are not yet supported"

data ExpressionLeaf = Oper Primitive | Value ExpInt
instance Show ExpressionLeaf where
  show    (Oper   x)  = show      x
  show    (Value  x)  = show      x
instance IExpression ExpressionLeaf where
  upcast  (Oper   x)  = upcast    x
  upcast  (Value  x)  = upcast    x
  isList  (Oper   x)  = isList    x
  isList  (Value  x)  = isList    x
  isInt   (Oper   x)  = isInt     x
  isInt   (Value  x)  = isInt     x
  isNil   (Oper   x)  = isNil     x
  isNil   (Value  x)  = isNil     x
  eval    (Oper   x)  = eval      x
  eval    (Value  x)  = eval      x
  apply   (Oper   x)  = apply     x  
  apply   (Value  x)  = apply     x  

data ExpInt = ExpInt Int
instance Show ExpInt where 
  show    (ExpInt x)  = show      x
instance IExpression ExpInt where
  upcast    x         = Leaf (Value x)
  isList    _         = False
  isInt     _         = True
  isNil     _         = error "isNil should be applied to composite expression only"
  eval      x     _   = upcast    x -- self evaluating
  apply     _     _   = error "An integer is not an operator"
  
data Primitive = MkPlus Plus | MkMult Mult
instance Show Primitive where
  show    (MkPlus x)    = show x
  show    (MkMult Mult) = show Mult

instance IExpression Primitive where
  upcast  (MkPlus x)  = upcast    x
  upcast  (MkMult x)  = upcast    x
  isList  (MkPlus x)  = isList    x
  isList  (MkMult x)  = isList    x
  isInt   (MkPlus x)  = isInt     x
  isInt   (MkMult x)  = isInt     x
  isNil   (MkPlus x)  = isNil     x
  isNil   (MkMult x)  = isNil     x
  eval    (MkPlus x)  = eval      x
  eval    (MkMult x)  = eval      x
  apply   (MkPlus x)  = apply     x  
  apply   (MkMult x)  = apply     x  

data Plus = Plus
instance Show Plus where 
  show    _           = "+"
instance IExpression Plus where
  upcast  _           = Leaf (Oper (MkPlus Plus))
  isList  _           = False
  isInt   _           = False
  isNil   _           = error "isNil should be applied to composite expression only"
  eval    _   _       = upcast Plus -- self-evaluating
  apply               = plusApply   -- defined below 

data Mult = Mult
instance Show Mult where 
  show    _           = "*"
instance IExpression Mult where
  upcast  _           = Leaf (Oper (MkMult Mult))
  isList  _           = False
  isInt   _           = False
  isNil   _           = error "isNil should be applied to composite expression only"
  eval    _   _       = upcast Mult -- self-evaluating
  apply               = multApply   -- defined below 

consShow :: Cons -> String
consShow cons = foldLeft (MkCons cons) "(" operator ++ "\b)"  where
  operator = (\str -> \exp -> str ++ (show exp) ++ " ")

consEval :: Cons -> Environment -> Expression
consEval cons env = apply operator arguments where
  values = evalList (MkCons cons) env
  (operator, arguments) = case values of
    MkCons (Cons x y) -> (x,y)
    otherwise         -> error "Should not happen"

plusApply :: Plus ->  ExpressionComposite -> Expression
plusApply Plus args = upcast (ExpInt sum) where
  sum = foldLeft args 0 (\res -> \exp -> case exp of
    Leaf (Value (ExpInt x)) -> res + x
    otherwise               -> error "+: arguments is not a valid integer")

multApply :: Mult ->  ExpressionComposite -> Expression
multApply Mult args = upcast (ExpInt prod) where
  prod = foldLeft args 1 (\res -> \exp -> case exp of
    Leaf (Value (ExpInt x)) -> res * x
    otherwise               -> error "*: arguments is not a valid integer")

foldLeft  :: ExpressionComposite -> b -> (b -> Expression -> b) -> b
foldLeft list init oper = fold list init where
  fold (Comp Nil) acc = acc
  fold (MkCons (Cons car cdr)) acc = fold cdr (oper acc car)


foldRight :: ExpressionComposite -> b -> (Expression -> b -> b) -> b
foldRight (Comp Nil) init _                 = init
foldRight (MkCons (Cons car cdr)) init oper = oper car (foldRight cdr init oper)


evalList  :: ExpressionComposite -> Environment -> ExpressionComposite
evalList list env = foldRight list (Comp Nil) (\exp -> \args -> 
  (MkCons (Cons (eval exp env) args)))

nil :: ExpressionComposite
nil = Comp Nil

cons :: Expression -> ExpressionComposite -> ExpressionComposite
cons x y = MkCons (Cons x y)

plus :: Expression
plus = upcast Plus

mult :: Expression
mult = upcast Mult

expInt :: Int -> Expression
expInt x = upcast (ExpInt x)


main = do 
  let
    env   = Environment
    two   = expInt 2
    seven = expInt 7
    five  = expInt 5
    exp1  = upcast (cons plus (cons two (cons seven (cons five nil))))
    exp2  = upcast (cons mult (cons two (cons exp1  (cons five nil))))
    in
    putStrLn ("The evaluation of the Lisp expression: " ++ (show exp2)) >>
    putStrLn ("yields the value: " ++ (show (eval exp2 env)))




