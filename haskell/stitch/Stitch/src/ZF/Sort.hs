{-# LANGUAGE GADTs          #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module ZF.Sort  
  ( Sort  (..)
  , SSort (..)
  ) where

import Data.Kind

-- | Possible sorts for the ZF language
-- Prop   : propositions
-- Set    : sets
-- (:->:) : Function sorts created out of Prop and Set
data Sort = Prop | Set | Sort :->: Sort

infixr 5 :->:

-- | Singleton type for Sort
data SSort :: Sort -> Type where
  SProp    :: SSort 'Prop
  SSet     :: SSort 'Set
  (:%->:)  :: SSort srt1 -> SSort srt2 -> SSort (srt1 ':->: srt2)

infixr 5 :%->:
