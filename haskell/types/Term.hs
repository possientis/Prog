{-# LANGUAGE ViewPatterns #-}

module Term 
  ( Term(..)
  , eval1
  ) where 

data Term
  = TmTrue
  | TmFalse
  | TmIf Term Term Term 
  | TmZero 
  | TmSucc Term
  | TmPred Term
  | TmIsZero Term
  deriving (Eq, Show)

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

eval :: Term -> Maybe Term
eval t = case eval1 t of
  Just t1 -> eval t1
  Nothing -> if isVal t then Just t else Nothing

eval' :: Term -> Maybe Term
eval' v@(isVal -> True)                                         = Just v
eval' (TmIf (eval' -> Just TmTrue) t2 t3)                       = eval' t2
eval' (TmIf (eval' -> Just TmFalse)t2 t3)                       = eval' t3
eval' (TmSucc t1@(isNumerical -> True))                         = Just $ TmSucc t1 
eval' (TmPred (eval' -> Just TmZero))                           = Just TmZero
eval' (TmPred (eval' -> Just (TmSucc t2@(isNumerical -> True))))= Just t2
eval' (TmIsZero (eval' -> Just TmZero))                         = Just TmTrue 
eval' (TmIsZero (TmSucc (isNumerical -> True)))                 = Just TmFalse





