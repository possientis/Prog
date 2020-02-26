module  Promotion
    (   item
    ,   result
    )   where

import Control.Lens

data Promotion a = Promotion
    { _item :: a
    , _discountPercentage :: Double
    } deriving (Show)

item :: Lens (Promotion a) (Promotion b) a b
item = lens getter setter where
    getter :: Promotion a -> a
    getter = _item
    setter :: Promotion a -> b -> Promotion b
    setter promo newItem = promo { _item = newItem }

-- Can't write a lens here
data Preferences a = Preferences
    { _best  :: a
    , _worst :: a
    } deriving (Show)

data Result e = Result
    { _lineNumber :: Int
    , _result     :: Either e String
    } deriving (Show)

result :: Lens (Result e) (Result e') (Either e String) (Either e' String)
result = lens getter setter where
    getter :: Result e -> Either e String
    getter = _result
    setter :: Result e -> Either e' String -> Result e'
    setter res (Left err)      = res { _result = Left err }
    setter res (Right success) = res { _result = Right success }

