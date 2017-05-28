import Control.Category
import Control.Arrow

data Parser s a b = P (StaticParser s) (DynamicParser s a b)

data StaticParser s = SP Bool [s]
newtype DynamicParser s a b = DP ((a, [s]) -> (b, [s]))

spCharA :: Char -> StaticParser Char
spCharA c = SP False [c]

dpCharA :: Char -> DynamicParser Char Char Char 
dpCharA c = DP (\(_,x:xs) -> (x,xs))


charA :: Char -> Parser Char Char Char 
charA c = P (SP False [c]) (DP (\(_,x:xs) -> (x,xs)))


instance Category (Parser s) where
  id  = P (SP True []) (DP (\(a,s) -> (a,s)))
  (.) = undefined


instance Arrow (Parser s) where
  arr f = P (SP True []) (DP (\(b,s) -> (f b, s)))
  first (P sp (DP p)) = P sp (DP (\((b,d),s) -> let (c,s') = p (b,s) in ((c,d),s')))
