{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

module  Eval
    (   Eval    (..)    -- TODO: hide 
    )   where


import Data.Functor.Identity
import Control.Monad.Trans.State hiding (State)

import State

newtype Eval a = Eval { unEval :: StateT State Identity a } 
    deriving (Functor, Applicative, Monad)
