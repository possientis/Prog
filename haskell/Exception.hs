import Control.Monad.Catch
import Prelude hiding (pure)


data MyException = MyException
    deriving (Show)


instance Exception MyException


example :: MonadCatch m => Int -> Int -> m Int
example x y | y == 0    = throwM MyException
            | otherwise = return $ x `div` y


pure :: MonadCatch m => m (Either MyException Int)
pure = do
    a <- try (example 1 2)
    b <- try (example 15 0)
    return (a >> b)


main :: IO ()
main = do
    x <- pure
    putStrLn $ show x
