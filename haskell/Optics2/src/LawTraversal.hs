module  LawTraversal
    (   ex1, ex2, ex3, ex4, ex5, ex6, ex7
    )   where

import Control.Lens
import Control.Applicative

-- traverseOf myTraversal pure x == pure x

ex1 :: [(String,String)]
ex1 = traverseOf both pure ("don't","touch")

ex2 :: [(String, String)]
ex2 = pure ("don't","touch")

ex3 :: Maybe (String,String)
ex3 = traverseOf both pure ("don't","touch")

ex4 :: Maybe (String,String)
ex4 = pure ("don't","touch")

ex5 :: [(String,String)]
ex5 = traverseOf both (\s -> [s ++ "!"]) ("don't","touch")


badTupleSnd :: Traversal (Int,a) (Int,b) a b
badTupleSnd f (n,a) = liftA2 (,) (pure (n + 1)) (f a)

ex6 :: [(Int, String)]
ex6 = traverseOf badTupleSnd pure (10, "Yo")

ex7 :: [(Int, String)]
ex7 = pure (10, "Yo")


-- fmap (traverseOf myTraversal f) .  traversalOf myTraversal g $ x
-- ==
-- getCompose . traverseOf myTraversal (Compose . fmap f . g) $ x

-- if the effect is the Identity functor
--
-- x & myTraversal %~ f 
--   & myTraversal %~ g
-- ==
-- x & myTraversal %~ (g . f)


