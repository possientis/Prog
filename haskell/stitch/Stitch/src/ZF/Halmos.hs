{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module ZF.Halmos
  ( lAnd
  , lNot
  , lOr
  , (===)
  ) where


import Stitch.Data.Vec

import ZF.TExp
import ZF.Sort

-- | Convenient reference to first free variable in context
_0 :: TExp (srt ':> ctx) srt
_0  = Var EZ

-- | Convenient reference to second free variable in context
_1 :: TExp (srt0 ':> srt ':> ctx) srt
_1  = Var (ES EZ)

-- | Convenient reference to second free variable in context
_2 :: TExp (srt0 ':> srt1 ':> srt ':> ctx) srt
_2  = Var (ES (ES EZ))

-- | Abstracting over a propositional variable
pLam :: TExp ('Prop ':> ctx) srt -> TExp ctx ('Prop ':->: srt)
pLam = Lam SProp

-- | Abstracting over a set variable
sLam :: TExp ('Set ':> ctx) srt -> TExp ctx ('Set ':->: srt)
sLam = Lam SSet

-- | Sugar
(==>) :: TExp ctx 'Prop -> TExp ctx 'Prop -> TExp ctx 'Prop
(==>) = Imp

-- | Logical not: \p:Prop. p => Bot
lNot :: TExp ctx ('Prop ':->: 'Prop)
lNot = pLam $ _0 ==> Bot

-- | Sugar
fNot :: TExp ctx 'Prop -> TExp ctx 'Prop
fNot = App lNot

-- | Logical or: \p:Prop. \q:Prop. not p => q
lOr :: TExp ctx ('Prop ':->: 'Prop ':->: 'Prop)
lOr = pLam $ pLam $ (fNot _1) ==> _0

-- | Sugar
fOr :: TExp ctx 'Prop -> TExp ctx 'Prop -> TExp ctx 'Prop
fOr e1 e2 = App (App lOr e1) e2

-- | Logical and: \p:Prop. \q:Prop. not (not p \/ not q)
lAnd :: TExp ctx ('Prop ':->: 'Prop ':->: 'Prop)
lAnd = pLam $ pLam $ fNot $ fOr (fNot _1) (fNot _0)

-- | Sugar
fAnd :: TExp ctx 'Prop -> TExp ctx 'Prop -> TExp ctx 'Prop
fAnd e1 e2 = App (App lAnd e1) e2

-- | Logical equivalence: \p:Prop. \q:Prop. (p => q) /\ (q => p)
lEquiv :: TExp ctx ('Prop ':->: 'Prop ':->: 'Prop)
lEquiv = pLam $ pLam $ fAnd (_1 ==> _0) (_0 ==> _1) 

-- | Sugar
(<==>) :: TExp ctx 'Prop -> TExp ctx 'Prop -> TExp ctx 'Prop
(<==>) e1 e2 = App (App lEquiv e1) e2

-- | Equality between sets : \x:Set. \y:Set. 
--     (forall z. (z:x) <=> (z:y)) && (forall z. (x:z) <=> (y:z))
--  Two sets are equal if they have the same elements, and are elements
--  of the same sets. The ZF axiom of extentionality states that it is 
--  in fact sufficient to have the same elements in order for two sets
--  to be equal. So this axiom effectively posits that having the same 
--  elements implies being elements of the same sets. 
--  Note that for any predicate P and sets x y, we should be able to prove
--  x = y => P x => P y. Otherwise, there is something wrong in our 
--  definition of equality, our type expression language or our proof system.
(===) :: TExp ctx ('Set ':->: 'Set ':->: 'Prop)
(===) = sLam $ sLam $ fAnd 
  (All $ (In _0 _2) <==> (In _0 _1))
  (All $ (In _2 _0) <==> (In _1 _0))

-- | universal quanitification can itself be expressed as a type expression
--   of sort (Set -> Prop) -> Prop.
-- Forall = \f:(Set -> Prop). forall x. f x
lForall :: TExp ctx (('Set ':->: Prop) ':->: 'Prop)
lForall = Lam (SSet :%->: SProp) $ All (App _1 _0)

fForall :: TExp ctx ('Set ':->: Prop) -> TExp ctx 'Prop
fForall = App lForall

all' :: TExp ('Set ':> ctx) 'Prop -> TExp ctx 'Prop
all' open = fForall (sLam open)



