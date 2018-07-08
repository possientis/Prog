{-# LANGUAGE DeriveFunctor #-}

import Control.Monad
import Control.Monad.State
import Data.Map.Strict

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

data AExp
    = ANum Int
    | AVar Var
    | APlus AExp AExp
    | AMinus AExp AExp
    | AMult AExp AExp

data BExp
    = BTrue
    | BFalse
    | BEq AExp AExp
    | BLe AExp AExp
    | BNot BExp
    | BAnd BExp BExp

data Com
    = CSkip
    | CAss Var AExp
    | CSeq Com Com
    | CIf BExp Com Com
    | CWhile BExp Com

data ComF a
    = FSkip a
    | FAss Var AExp a
    | FIf BExp Com Com a
    | FWhile BExp Com a
    deriving Functor

type Command = Free ComF


compile :: Com -> Command ()
compile CSkip = Pure ()
compile (CAss x a) = Free $ FAss x a (Pure ())
-- TODO


type Dict = Map Var Int

aeval :: Dict -> AExp -> Int
aeval e a = undefined 

beval :: Dict -> BExp -> Bool
beval e b = undefined





