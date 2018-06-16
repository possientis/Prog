--{-# LANGUAGE TemplateHaskell #-}

import Control.Lens

data Example a = Example { _foo :: Int, _bar :: a }


--makeLenses ''Example


foo :: Lens' (Example a) Int
--  :: Functor f => (Int -> f Int) -> (Example a -> f (Example a))  ;; expand alias
foo = undefined


