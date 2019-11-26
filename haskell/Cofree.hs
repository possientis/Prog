{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

import Control.Comonad

data Cofree f a = a :< (f (Cofree f a))

instance (Functor f) => Functor (Cofree f) where
    fmap f (x :< xs) = f x :< fmap (fmap f) xs

instance (Functor f) => Comonad (Cofree f) where
    extract (x :< _) = x
    duplicate x@(_ :< xs) = x :< fmap duplicate xs

data Fix f = Fix { unFix :: f (Fix f) }

forget :: (Functor f) => Cofree f a -> Fix f
forget (_ :< xs) = Fix (fmap forget xs) 

cata :: (Functor f) => (f a -> a) -> Fix f -> a
cata g (Fix x) = g  (fmap (cata g) x)  

ana :: (Functor f) => (a -> f a) -> a -> Fix f
ana g x = Fix (fmap (ana g) (g x))

data CofreeF f a r = CofreeF a (f r)

instance (Functor f) => Functor (CofreeF f a) where 
    fmap g (CofreeF a x) = CofreeF a (fmap g x)

to :: (Functor f) => Cofree f a -> Fix (CofreeF f a)
to (x :< xs) = Fix (CofreeF x (fmap to xs))

from :: (Functor f) => Fix (CofreeF f a) -> Cofree f a
from (Fix (CofreeF a x)) = a :< fmap from x

fromto :: (Functor f) => Cofree f a -> Cofree f a
fromto = from . to

-- fromto (x :< xs) = from (to (x :< xs))                   <-- definition of fromto
--                  = from (Fix (CofreeF x (fmap to xs)))   <-- definition of to
--                  = x :< fmap from (fmap to xs)           <-- definition of from
--                  = x :< fmap (from . to) xs              <-- functor law for f
--                  = x :< fmap fromto xs                   <-- definition of fromto
--                  = x :< xs                               <-- why ?

-- why lemma1 = id?
lemma1 :: (Functor f) => Cofree f a -> Cofree f a
lemma1 (x :< xs) = x :< fmap lemma1 xs

tofrom :: (Functor f) => Fix (CofreeF f a) -> Fix (CofreeF f a) 
tofrom  = to . from 

-- tofromf (Fix (CofreeF a x))  = to (from (Fix (CofreeF a x)))             <-- definition of tofrom
--                              = to (a :< fmap from x)                     <-- definition of from 
--                              = Fix (CofreeF a (fmap to (fmap from x)))   <-- definition of to
--                              = Fix (CofreeF a (fmap (to . from) x))      <-- functor law for f
--                              = Fix (CofreeF a (fmap tofrom x))           <-- definition of tofrom
--                              = Fix (CofreeF a x)                         <-- why ?

-- why lemma2 = id?
lemma2 :: (Functor f) => Fix (CofreeF f a) -> Fix (CofreeF f a)
lemma2 (Fix (CofreeF a x)) = Fix (CofreeF a (fmap lemma2 x))





