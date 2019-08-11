{-# LANGUAGE RankNTypes     #-}
-- types 'a' and 'forall r . (a -> r) -> r' are isomorphic

-- appears to be a particular case of Yoneda when F = I
-- F : C -> Set 
-- F a ~ Nat[C(a,-), F]

to :: a -> (forall r . (a -> r) -> r)
to a f = f a

from :: (forall r . (a -> r) -> r) -> a
from f = f id

newtype Cont a = Cont { unCount :: forall r . (a -> r) -> r }

runCount :: Cont a -> a
runCount (Cont f) = f id

instance Functor Cont where
    fmap f (Cont a) = Cont $ \h -> a (h . f)

instance Applicative Cont where
    pure a = Cont $ \h -> h a
    (Cont f) <*> (Cont a) = Cont $ \h -> h ((f id) (a id))

instance Monad Cont where
    return = pure
    (Cont a) >>= g = Cont $ \h -> 
        let (Cont b) = g (a id) in h (b id) 


withVersionNumber :: (Double -> r) -> r
withVersionNumber f = f 1.0

withTimestamp :: (Int -> r) -> r
withTimestamp f = f 1532083362

withOS :: (String -> r) -> r
withOS f = f "linux"


-- 'pyramid of doom' style
releaseString :: String
releaseString =
    withVersionNumber $ \version ->
        withTimestamp $ \date ->
            withOS $ \os ->
                os ++ "-" ++ show version ++ "-" ++ show date

releaseStringCont :: String
releaseStringCont = runCount $ do
    version <- Cont withVersionNumber
    date    <- Cont withTimestamp
    os      <- Cont withOS
    return $ os ++ "-" ++ show version ++ "-" ++ show date
    

main :: IO ()
main = do
    putStrLn releaseString
    putStrLn releaseStringCont





