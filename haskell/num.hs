import Data.List

data Op = Plus | Minus | Mul | Div | Pow deriving (Eq, Show)

data Exp a  = Number a
            | Symbol String
            | BinaryArith Op (Exp a) (Exp a)
            | UnaryArith String (Exp a) 
  deriving Eq

instance Num a => Num (Exp a) where
  a + b = BinaryArith Plus a b
  a - b = BinaryArith Minus a b
  a * b = BinaryArith Mul a b
  negate a = BinaryArith Mul (Number (-1)) a
  abs a = UnaryArith "abs" a
  signum _ = error "signum is unimplemented"
  fromInteger i = Number (fromInteger i)

instance Fractional a => Fractional (Exp a) where
  a / b = BinaryArith Div a b
  recip a = BinaryArith Div (Number 1) a
  fromRational r = Number (fromRational r)


