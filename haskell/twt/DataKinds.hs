{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- to run with latest version 
-- :!stack ghci --ghci-options -XDataKinds %  

import Data.Proxy

-- needed to promoted builtin types, Symbol etc..
import GHC.TypeLits

-- Data constructors become valid types and types become valid kinds

-- Bool remains a type and True & False remain values
v1 :: Bool
v1 = True

v2 :: Bool
v2 = False


-- but True and False also exist at the type level
type T1 = True
type T2 = False

type T3 = 'True
type T4 = 'False

-- In this case you'll need the apostrophy.
-- We have the type  Unit of kind *
-- We have the type 'Unit of kind Unit
data Unit = Unit

-- gives access to types 'TUser and 'TAdmin of kind UserType
data UserType = TUser | TAdmin 

data User = User 
    { userAdminToken :: Maybe (Proxy 'TAdmin)
--  , other stuff
    }

doSensitiveThings :: Proxy 'TAdmin -> IO ()
doSensitiveThings = undefined


type T5 = "hello"               -- kind Symbol
type T6 = "world"               -- kind Symbol 

-- 'kind! T7' evaluates to "helloworld"
type T7 = AppendSymbol T5 T6    -- kind Symbol

-- 'kind! T8' evaluates to 'LT
type T8 = CmpSymbol T5 T6       -- kind Ordering

type T9 = 65656                 -- kind Nat

-- 'kind! T10' evaluates to 3
type T10 = 1 + 2                -- kind Nat

-- 'kind! T11' evaluates to 128
type T11 = 256 `Div` 2          -- kind Nat


type T12 = '[]                  -- kind [*]

type T13 = '(:)                 -- kind * -> [*] -> [*]


type T14 = Int : T12            -- kind [*]
type T15 = String : T14         -- kind [*]

type T16 =  [Bool]              -- kind *
type T17 = '[Bool]              -- kind [*]

type T18 = '[ 'True ]           -- kind [Bool]
--type T19 = '['True]           -- parse error, beware !

type T20 = '(2,"tuple")         -- kind (Nat,Symbol)

    
