module  Syntax
    (   Exp (..)
    ,   Val (..)
    )   where

import Data.Text
import Data.Word
import Data.Int

data Lit 
    = LInt64  Int64
    | LWord64 Word64
    | LFloat  Float
    | LBool   Bool
    | LString String
    | LChar   Char
    deriving (Eq, Ord, Show)

newtype Name = Name { unName :: Text }  deriving (Eq, Ord, Show)

data SVal = Unit | Lit Lit | Var Name   deriving (Eq, Ord, Show)

data Val = Node Name [SVal] | Simp SVal deriving (Eq, Ord, Show)
    
data Exp
    = Bind Exp Val Exp
    | Case Val [(Val,Exp)]
    | App Name [SVal]
    | Pure Val
    | Store Val
    | Fetch Name 
    | Update Name Val
    deriving (Eq, Ord, Show)
    

