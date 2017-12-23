{-# LANGUAGE ExistentialQuantification, RankNTypes #-}


data Box = forall a . Box a (a -> a) (a -> String)

boxa :: Box
boxa = Box 1 negate show

boxb :: Box
boxb = Box "foo" reverse show

apply :: Box -> String
apply (Box x f p) = p (f x)

data SBox = forall a. Show a => SBox a

boxes :: [SBox]
boxes = [SBox (), SBox 2, SBox "foo"]

showBox :: SBox -> String
showBox (SBox x) = show x


main :: IO ()
main = mapM_ (putStrLn . showBox) boxes


data MonadI m = MonadI
    {   return_ :: forall a. a -> m a
    ,   bind_   :: forall a b. m a -> (a -> m b) -> m b
    } 

monadMaybe :: MonadI Maybe
monadMaybe = MonadI
    {   return_ = Just
    ,   bind_ = \m f -> case m of
            Nothing -> Nothing
            Just x  -> f x
    }
