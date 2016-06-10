-- nat in coq
data Nat = O | S Nat

-- corresponds to coq's positive type
data Positive = XH | XO Positive | XI Positive

-- Psucc in coq
pSucc :: Positive -> Positive
pSucc XH      = XO XH
pSucc (XO x)  = XI x
pSucc (XI x)  = XO (pSucc x)

-- list a in coq
data CoqList a = Nil | Cons a (CoqList a)

-- app in coq
app :: CoqList a -> CoqList a -> CoqList a
app Nil m         = m
app (Cons a l) m  = Cons a (app l m)

-- option a in coq
data Option a = Some a | None

-- nth' in coq
nth' :: CoqList a -> Nat -> Option a
nth'  Nil _           = None
nth' (Cons a l) O     = Some a
nth' (Cons a l) (S p) = nth' l p 




