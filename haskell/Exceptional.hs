data Exceptional e a = Success a | Exception e
  deriving (Show)

instance Monad (Exceptional e) where
  return = Success
  Exception l >>= _ = Exception l
  Success r   >>= k = k r

throw :: e -> Exceptional e a
throw = Exception

catch :: Exceptional e a -> (e -> Exceptional e a) -> Exceptional e a
catch (Exception l) h = h l
catch (Success r) _ = Success r


-- can we apply this to a reasonable situation

divide :: Integer -> Integer -> Rational
divide x y = (toRational x) / (toRational y)

divide' :: Integer -> Integer -> Exceptional String Rational
divide' x 0 = Exception "Divide by zero"
divide' x y = Success $ (toRational x) / (toRational y)


handle :: String -> Exceptional String Rational
handle e = case e of
            "Divide by zero"  -> Success 0


test = catch (divide' 3 0) handle


newtype ExceptionalT e m a =
  ExceptionalT { runExceptionalT :: m (Exceptional e a) }

instance Monad m => Monad (ExceptionalT e m) where
  return = ExceptionalT . return . Success
  m >>= k = ExceptionalT $
    runExceptionalT m >>= \a ->
      case a of
        Exception e -> return (Exception e)
        Success r   -> runExceptionalT (k r) 
    
    

 
