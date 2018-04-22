{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}



data (a :: k1) :=: (b :: k2) where
    HRefl :: a :=: a

-- abstract; the type Int is represented by the one value of type TyCon Int
data TyCon (a :: k) where
    MkTyCon :: TyCon a 

tyCon :: TyCon a
tyCon = MkTyCon


data TypeRep (a :: k) where
    TyCon :: TyCon a -> TypeRep a
    TyApp :: TypeRep a -> TypeRep b -> TypeRep (a b)

eqTyCon :: forall (a :: k1) (b :: k2). 
    TyCon a -> TyCon b -> Maybe (a :=: b)
eqTyCon = undefined


eqT :: forall (a :: k1) (b :: k2).
    TypeRep a -> TypeRep b -> Maybe (a :=: b)
eqT (TyCon t1) (TyCon t2)       = eqTyCon t1 t2
eqT (TyApp a1 b1) (TyApp a2 b2) 
    | Just HRefl <- eqT a1 a2
    , Just HRefl <- eqT b1 b2   = Just HRefl
eqT _ _                         = Nothing

data Dyn where
    Dyn :: forall (a :: *) . TypeRep a -> a -> Dyn

dynApply :: Dyn -> Dyn -> Maybe Dyn
dynApply (Dyn (TyApp 
                (TyApp (TyCon tarrow) targ)
                tres )
              fun)
         (Dyn targ' arg)
    | Just HRefl <- eqTyCon tarrow (tyCon :: TyCon (->))
    , Just HRefl <- eqT targ targ'
    = Just (Dyn tres (fun arg))

dynApply _ _ = Nothing



