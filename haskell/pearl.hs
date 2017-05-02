-- more parsing 
import Control.Applicative
import Control.Monad

newtype Parser a = Parser { run :: String -> [(a,String)] }

parser :: (String -> [(a,String)]) -> Parser a
parser = Parser

item :: Parser Char
item = parser (\cs -> case cs of 
                        ""      -> []         -- failure
                        (c:cs)  -> [(c,cs)])

instance Functor Parser where
  fmap = liftM

instance Applicative Parser where
  pure = return 
  (<*>) = ap

instance Monad Parser where
  return a  = parser (\cs -> [(a,cs)])
  m >>= f   = parser (\cs -> concat [ run (f a) cs' | (a, cs') <- run m cs ])


instance MonadPlus Parser where
  mzero = parser (\cs -> [])
  

p :: Parser (Char, Char)
p = do
  c <- item
  item
  d <- item
  return (c,d)



