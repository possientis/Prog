{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}

module  Optics.Bool
    (   SBool   (..)
    )   where

import Data.Kind

data SBool (b :: Bool) :: Type where
    STrue  :: SBool 'True
    SFalse :: SBool 'False 


