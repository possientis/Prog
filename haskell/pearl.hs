-- more parsing 

newtype Parser a = Parser { run :: String -> [(a,String)] }

parser :: (String -> [(a,String)]) -> Parser a
parser = Parser

item :: Parser Char
item = parser (\cs -> case cs of 
                        ""      -> []         -- failure
                        (c:cs)  -> [(c,cs)])

instance Monad Parser where
  return a  = parser (\cs -> [(a,cs)])
