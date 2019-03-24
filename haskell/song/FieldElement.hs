module  FieldElement
    (   FieldElement
    ,   field
    ,   inv
    )   where


data FieldElement = FieldElement
    { _num   :: Integer
    , _prime :: Integer
    } deriving (Eq)

field :: Integer -> Integer -> FieldElement
field x p
    | p <= 1     = error "field: p should be a prime number"
    | otherwise  = FieldElement (x `mod` p) p

instance Show FieldElement where
    show (FieldElement x p) = "(" ++ (show $ x `mod` p) ++ "::F_" ++ show p ++ ")"


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
    

inv :: FieldElement -> FieldElement
inv f@(FieldElement x p)
    | x `mod` p == 0    = error "inv: Zero has no inverse"
    | otherwise         = pow f (p-2)

instance Fractional FieldElement where
    (/) f1@(FieldElement _ p) f2@(FieldElement y q)
        | p /= q         = error "(/) : Type mismatch in FieldElement"
        | y `mod` p == 0 = error "(/) : Division by zero"
        | otherwise      = f1 * inv f2
    recip = inv
    fromRational _       = error "fromRational: do not use for FieldElement"





