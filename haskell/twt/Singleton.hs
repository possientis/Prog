{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilyDependencies     #-}


import Data.Kind
import Data.Constraint (Dict (..))
import Data.Foldable (for_)
import Control.Monad.Trans.Writer

data SBool (b :: Bool) :: Type where
    STrue  :: SBool 'True
    SFalse :: SBool 'False


fromSBool :: SBool b -> Bool
fromSBool STrue  = True
fromSBool SFalse = False

data SomeSBool where
    SomeSBool :: SBool b -> SomeSBool

withSomeSBool 
    :: SomeSBool
    -> (forall (b :: Bool) . SBool b -> r )
    -> r
withSomeSBool (SomeSBool s) f = f s


toSBool :: Bool -> SomeSBool
toSBool True  = SomeSBool STrue
toSBool False = SomeSBool SFalse 

b1 :: Bool
b1 = withSomeSBool (toSBool True) fromSBool

b2 :: Bool 
b2 = withSomeSBool (toSBool False) fromSBool

b3 :: SomeSBool
b3 = toSBool (fromSBool STrue)

b4 :: SomeSBool
b4 = toSBool (fromSBool SFalse)


instance Show SomeSBool where
    show s = withSomeSBool s (show . fromSBool)


class Monad (LoggingMonad b) => MonadLogging (b :: Bool) where
    type LoggingMonad b = (r :: Type -> Type) | r -> b
    logMsg :: String -> LoggingMonad b ()
    runLogging :: LoggingMonad b a -> IO a

instance MonadLogging 'False where
    type LoggingMonad 'False = IO
    logMsg _   = pure ()
    runLogging = id

instance MonadLogging 'True where
    type LoggingMonad 'True = WriterT [String] IO
    logMsg s = tell [s]
    runLogging m = do
        (a, w) <- runWriterT m
        for_ w putStrLn
        pure a


program :: MonadLogging b => LoggingMonad b ()
program = do
    logMsg "hello world!"
    pure ()


main :: IO ()
main = do
    print b1
    print b2
    print b3
    print b4
    bool <- read <$> getLine
    withSomeSBool (toSBool bool) $
        \(sb :: SBool b) -> 
            case dict @MonadLogging sb of
                Dict -> runLogging @b program

dict :: ( c 'True, c 'False) => SBool b -> Dict (c b)
dict STrue  = Dict
dict SFalse = Dict
