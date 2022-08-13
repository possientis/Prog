{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeInType       #-}

module Stitch.Globals
  ( Globals
  , emptyGlobals
  , extend
  , lookupGlobal
  ) where

import Control.Monad.Except
import Data.Map                       as Map
import Text.PrettyPrint.ANSI.Leijen
import Type.Reflection

import Stitch.Data.Exists
import Stitch.Data.Vec

import Stitch.Exp

newtype Globals = Globals (Map String (SingEx (Exp 'VNil)))

-- | An empty global variable environment
emptyGlobals :: Globals
emptyGlobals  = Globals Map.empty

-- | Extend a 'Globals' with a new binding
--   Note that 'withTypeable sty' is needed to bring the constraint
--  'Typeable ty' into scope (and so 'SingI ty'), which is needed to 
--   use the data constructor SingEx.
extend :: String -> TypeRep ty -> Exp 'VNil ty -> Globals -> Globals
extend var sty e (Globals globals)
  = Globals $ insert var (withTypeable sty $ SingEx e) globals

-- | Lookup a global variable. Fails with 'throwError' if variable not bound.
lookupGlobal 
  :: MonadError Doc m
  => Globals 
  -> String
  -> (forall ty. TypeRep ty -> Exp 'VNil ty -> m r)
  -> m r
lookupGlobal (Globals globals) var k
  = case Map.lookup var globals of
      Just e  -> unpackSingEx e k
      Nothing -> throwError 
        $  text "Global variable not in scope:" 
       <+> squotes (text var)
