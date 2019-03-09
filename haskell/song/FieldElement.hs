module  FieldElement
    (   FieldElement    (..)
    )   where

data FieldElement = FieldElement
    { num   :: Integer
    , prime :: Integer
    } deriving (Eq)

instance Show FieldElement where
    show (FieldElement x p) 
        = "FieldElement_" ++ (show p) ++ "(" ++ (show $ x `mod` p) ++ ")"


instance Num FieldElement where
    (+) (FieldElement x p) (FieldElement y q)
        | p /= q    = error "(+) : Type mismatch in FieldElement"
        | otherwise = FieldElement ((x + y) `mod` p) p
    (*) (FieldElement x p) (FieldElement y q)
        | p /= q    = error "(*) : Type mismatch in FieldElement"
        | otherwise = FieldElement ((x * y) `mod` p) p
    abs _           = error "abs : Should not be used for FieldElement"
    signum _        = error "signum: Should not be used for FieldElement"
    fromInteger _   = error "fromInteger: Should not be used for FieldElement"
    negate (FieldElement x p) = FieldElement ((-x) `mod` p) p
    



