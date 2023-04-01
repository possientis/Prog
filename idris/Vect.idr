import Data.Vect

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex n idx xs = 
  case integerToFin idx n of
        Nothing    => Nothing
        (Just idx) => Just (index idx xs) 

                 
