module  Traversable
    (   Traversable     (..)
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9
    )   where

-- Data.Traversable

import Prelude                  hiding (Traversable, traverse, sequenceA)
import Data.Char
import Control.Lens             hiding (Traversable, traverse)
import Control.Applicative
import Text.Read (readMaybe)

class (Functor t, Foldable t) => Traversable t where
    {-# MINIMAL traverse | sequenceA #-}
    
    traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
    traverse f = sequenceA . fmap f

    sequenceA :: Applicative f => t (f a) -> f (t a)
    sequenceA = traverse id 

    mapM :: Monad m => (a -> m b) -> t a -> m (t b)
    mapM = traverse

    sequence :: Monad m => t (m a) -> m (t a)
    sequence = sequenceA

instance Traversable Maybe where
    traverse _ Nothing = pure Nothing
    traverse f (Just x) = Just <$> f x 

instance Traversable [] where
    traverse _ [] = pure []
    traverse f (x : xs) =  liftA2 (:) (f x) (traverse f xs)

instance Traversable (Either a) where
    traverse _ (Left x) = pure (Left x)
    traverse f (Right y) = Right <$> f y

instance Traversable ((,) a) where
    traverse f (a,x) = ((,) a) <$> f x

ex1 :: Maybe [Int]
ex1 = traverse readMaybe ["1","2","3"]


ex2 :: Maybe [Int]
ex2 = traverse readMaybe ["1","fail","3"]

ex3 :: IO [String]
ex3 = traverse readFile ["src/Traversal.hs","src/Cards.hs"]

ex4 :: [(String,Int)]
ex4 = traverse (\n -> [n * 10, n * 100]) ("a",10)

-- simple
-- traverseOf :: Traversal s t a b -> (a -> f b) -> s -> f t

-- real
-- traverseOf :: LensLike f s t a b -> (a -> f b) -> s -> f t

ex5 :: Maybe (Int, Int)
ex5 = traverseOf both readMaybe ("1","2")


ex6 :: Maybe (Int, Int)
ex6 = traverseOf both readMaybe ("fail","2")

ex7 :: [(Char,Char)]
ex7 = traverseOf both (\c -> [toLower c, toUpper c]) ('a','b')

ex8 :: [(String,String)]
ex8 = traverseOf
    (both . traversed)
    (\c -> [toLower c, toUpper c])
    ("ab","cd")

validateEmail :: String -> Either String String
validateEmail email 
    | elem '@' email = Right email
    | otherwise      = Left ("missing '@': " ++ email)

ex9 :: Either String [(String,String)]
ex9 = traverseOf (traversed . _2) validateEmail
    [("Mike", "mike@tmnt.io")
    ,("Raph", "raph@tmnt.io")
    ,("Don",  "don@tmnt.io")
    ,("Leo",  "leo@tmnt.io")
    ]

