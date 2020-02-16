{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE ScopedTypeVariables    #-}


module  Template
    (
    )   where

import Data.Char
import Control.Lens
import Control.Applicative

import qualified Data.Map   as M
import qualified Data.Set   as S
import qualified Data.Text  as T 


