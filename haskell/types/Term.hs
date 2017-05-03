{-# LANGUAGE ViewPatterns #-}

data Term
  = TmTrue
  | TmFalse
  | TmIf Term Term Term 
  | TmZero 
  | TmSucc Term
  | TmPred Term
  | TmIsZero Term

isNumerical :: Term -> Bool
isNumerical (TmZero)    = True
isNumerical (TmSucc x)  = isNumerical x
isNumerical     _       = False

isVal :: Term -> Bool
isVal (TmTrue)               = True
isVal (TmFalse)              = False
isVal (isNumerical -> True) = True
isVal         _             = False

eval1 :: Term -> Maybe Term
eval1 (TmIf TmTrue t2 t3)     = Just t2
eval1 (TmIf TmFalse t2 t3)    = Just t3
eval1 (TmIf t1 t2 t3)         = eval1 t1 >>= (\t1' -> Just $ TmIf t1' t2 t3)
eval1 (TmSucc t1)             = eval1 t1 >>= (\t1' -> Just $ TmSucc t1')
eval1 (TmPred TmZero)         = Just TmZero
eval1 (TmPred (TmSucc nv1))   | isNumerical nv1 = Just nv1
eval1 (TmPred t1)             = eval1 t1 >>= (\t1' -> Just $ TmPred t1')
eval1 (TmIsZero TmZero)       = Just TmTrue
eval1 (TmIsZero (TmSucc nv1)) | isNumerical nv1 = Just TmFalse
eval1 (TmIsZero t1)           = eval1 t1 >>= (\t1' -> Just $ TmIsZero t1')
eval1 _                       = Nothing



