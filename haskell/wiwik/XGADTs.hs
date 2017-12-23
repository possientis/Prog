import Control.Monad
import System.Directory
import Data.List
import System.IO
import Test.QuickCheck

-- -XGADTs 

data T a = T2 | T1 Bool deriving Show

f :: T a -> Bool -> Bool
f (T1 z) y = True
f T2 y = y

data Term a where
  Lit     :: Int -> Term Int
  Succ    :: Term Int -> Term Int
  IsZero  :: Term Int -> Term Bool
  If      :: Term Bool -> Term a -> Term a -> Term a

eval :: Term a -> a
eval (Lit i)      = i
eval (Succ t)     = 1 + eval t
eval (IsZero i)   = eval i == 0
eval (If b e1 e2) = if  eval b then eval e1 else eval e2

