import Syntax

data EvalException = NoRuleApplies


eval1 :: Term -> Either EvalException Term

eval1 (TmIf _ (TmTrue  _) t2 t3)    = Right t2

eval1 (TmIf _ (TmFalse _) t2 t3)    = Right t3

eval1 (TmIf fi t1 t2 t3)            = 
    case eval1 t1 of
        Left e                      -> Left e
        Right t1'                   -> Right $ TmIf fi t1' t2 t3

eval1 (TmSucc fi t1)                = 
    case eval1 t1 of
        Left e                      -> Left e
        Right t1'                   -> Right $ TmSucc fi t1'

eval1 (TmPred _ (TmZero _))         = Right $ TmZero dummyInfo 

eval1 (TmPred _ (TmSucc _ nv1))     
    | isNumerical nv1               = Right nv1

eval1 (TmPred fi t1)                = 
    case eval1 t1 of
        Left e                      -> Left e
        Right t1'                   -> Right $ TmPred fi t1' 

eval1 (TmIsZero _ (TmZero _))       = Right $ TmTrue dummyInfo

eval1 (TmIsZero _ (TmSucc _ nv1))
    | isNumerical nv1               = Right $ TmFalse dummyInfo

eval1 (TmIsZero fi t1)              =
    case eval1 t1 of
        Left e                      -> Left e
        Right t1'                   -> Right $ TmIsZero fi t1'
eval1 _                             = Left NoRuleApplies


eval :: Term -> Term
eval t = case eval1 t of
    Left _      -> t
    Right t'    -> eval t'

ex1 = eval (TmPred dummyInfo (TmSucc dummyInfo (TmZero dummyInfo)))









