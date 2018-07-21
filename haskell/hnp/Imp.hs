{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}

import Prelude hiding (lookup)
import Control.Monad
import Control.Monad.State
import Data.Map.Strict
import Data.Default

data Free f a = Pure a | Free (f (Free f a))

instance Functor f => Functor (Free f) where
    fmap                    = liftM

instance Functor f => Applicative (Free f) where
    pure                    = return
    (<*>)                   = ap

instance Functor f => Monad (Free f) where
    return                  = Pure
    (>>=) (Pure a) g        = g a
    (>>=) (Free k) g        = Free $ fmap (>>= g) k 

newtype Var = Var { unVar :: Int } deriving (Eq, Ord)

instance Show Var where
    show (Var 0) = "x"
    show (Var 1) = "y"
    show (Var 2) = "z"
    show (Var 3) = "t"
    show (Var 4) = "u"
    show (Var 5) = "v"
    show (Var n) = "x" ++ show (n - 6)

x = Var 0
y = Var 1
z = Var 2
t = Var 3
u = Var 4
v = Var 5


type Env = Map Var Int

data AExp
    = ANum Int
    | AVar Var
    | APlus AExp AExp
    | AMinus AExp AExp
    | AMult AExp AExp

aeval :: Env -> AExp -> Int
aeval e (ANum n) = n
aeval e (APlus  a1 a2)  = aeval e a1 + aeval e a2
aeval e (AMinus a1 a2)  = aeval e a1 - aeval e a2
aeval e (AMult  a1 a2)  = aeval e a1 * aeval e a2
aeval e (AVar x)        = case lookup x e of 
    Nothing     -> error "Unbound variable"
    (Just v)    -> v 


instance Show AExp where
    show (ANum n)       = show n
    show (AVar v)       = show v 
    show (APlus a1 a2)  = "(" ++ show a1 ++ "+" ++ show a2 ++ ")" 
    show (AMinus a1 a2) = "(" ++ show a1 ++ "-" ++ show a2 ++ ")" 
    show (AMult a1 a2)  = "(" ++ show a1 ++ "*" ++ show a2 ++ ")" 


data BExp
    = BTrue
    | BFalse
    | BEq AExp AExp
    | BLe AExp AExp
    | BNot BExp
    | BAnd BExp BExp


instance Show BExp where
    show BTrue          = "#t"
    show BFalse         = "#f"
    show (BEq a1 a2)    = "(" ++ show a1 ++ "==" ++ show a2 ++ ")" 
    show (BLe a1 a2)    = "(" ++ show a1 ++ "<=" ++ show a2 ++ ")" 
    show (BNot b)       = "¬" ++ show b
    show (BAnd b1 b2)   = "(" ++ show b1 ++ "&&" ++ show b2 ++ ")"

beval :: Env -> BExp -> Bool
beval e BTrue           = True
beval e BFalse          = False
beval e (BEq a1 a2)     = aeval e a1 == aeval e a2
beval e (BLe a1 a2)     = aeval e a1 <= aeval e a2
beval e (BNot b)        = not $ beval e b
beval e (BAnd b1 b2)    = beval e b1 && beval e b2

data Com
    = CSkip
    | CAss Var AExp
    | CSeq Com Com
    | CIf BExp Com Com
    | CWhile BExp Com
    deriving Show

skip = CSkip

infix 8 $:=$
($:=$) :: Var -> AExp -> Com
($:=$) x a = CAss x a

infixr 2 $>>$
($>>$) :: Com -> Com -> Com
($>>$) c1 c2 = CSeq c1 c2
ifb = CIf
while = CWhile

data ComF a
    = FSkip a
    | FAss Var AExp a
    | FSeq a a
    | FIf BExp a a
    | FWhile BExp a
    deriving Functor

type Command = Free ComF

compile :: Com -> Command ()
compile CSkip           = Free $ FSkip (Pure ())
compile (CAss x a)      = Free $ FAss x a (Pure ()) 
compile (CSeq c1 c2)    = Free $ FSeq (compile c1) (compile c2)
compile (CIf b c1 c2)   = Free $ FIf b (compile c1) (compile c2)
compile (CWhile b c)    = Free $ FWhile b (compile c)


instance Show (Command ()) where
    show (Pure ())              = "NOP"
    show (Free (FSkip c))       = "SKIP;"   ++ show c
    show (Free (FAss x a c))    = show x    ++ ":=" ++ show a ++ ";" ++ show c 
    show (Free (FSeq c1 c2))    = show c1   ++ ";" ++ show c2
    show (Free (FIf b c1 c2))   = "IF "     ++ show b 
                                            ++ " THEN " 
                                            ++ show c1
                                            ++ " ELSE " 
                                            ++ show c2
                                            ++ " FI"
    show (Free (FWhile b c))    = "WHILE "  ++ show b
                                            ++ " DO "
                                            ++ show c
                                            ++ " END"
fact :: Com
fact =  z $:=$ (AVar x) $>>$
        y $:=$ (ANum 1) $>>$ (
        while (BNot (BEq (AVar z) (ANum 0))) $
            y $:=$ AMult (AVar y) (AVar z) $>>$
            z $:=$ AMinus (AVar z) (ANum 1)
        )





interpret :: (Default a) => Command a -> State Env a
interpret (Pure a)                  = return a
interpret (Free (FSkip next))       = interpret next
interpret (Free (FAss x a next))    = do
    e <- get
    put $ insert x (aeval e a) e
    interpret next
interpret (Free (FSeq c1 c2))       = interpret c1 >> interpret c2
interpret (Free (FIf b c1 c2))      = do
    e <- get
    if (beval e b)
        then interpret c1
        else interpret c2
interpret w@(Free (FWhile b c))       = do
    e <- get
    if (beval e b)
        then interpret c >> interpret w
        else return def 

env0 :: Env
env0 = insert x 5 empty 

run :: Command () -> Env
run c = let (_,e) = runState (interpret c) env0 in e

main :: IO ()
main = do
    print $ run $ compile fact


