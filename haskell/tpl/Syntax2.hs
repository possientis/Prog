
data Info = Info | DummyInfo deriving (Eq,Show)

newtype Length = Length Int

newtype Name = Name String

data Term
    = TmVar Info Int Length
    | TmLam Info Name Term
    | TmApp Info Term Term


 


