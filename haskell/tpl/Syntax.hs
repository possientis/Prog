module  Syntax  
    (   Term (..)
    ,   isNumerical
    ,   isVal
    ,   dummyInfo
    )   where


data Info = Info | DummyInfo

dummyInfo :: Info
dummyInfo = DummyInfo

data Term 
    = TmTrue    Info
    | TmFalse   Info
    | TmIf      Info Term Term Term
    | TmZero    Info
    | TmSucc    Info Term
    | TmPred    Info Term
    | TmIsZero  Info Term


isNumerical :: Term -> Bool
isNumerical (TmZero _)      = True
isNumerical (TmSucc _ t1)   = isNumerical t1 
isNumerical _               = False


isVal :: Term -> Bool
isVal (TmTrue _)        = True
isVal (TmFalse _)       = True
isVal t | isNumerical t = True
isVal _                 = False





