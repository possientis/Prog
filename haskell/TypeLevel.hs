{-# LANGUAGE GADTs, ExplicitForAll #-}

data Eql a b where
    Refl :: Eql a a

-- congruence
cong :: Eql a b -> Eql (f a) (f b)
cong Refl = Refl

-- reflexivity
refl :: Eql a a
refl = Refl

-- symmetry
sym :: Eql a b -> Eql b a
sym Refl = Refl

-- transitivity
trans :: Eql a b -> Eql b c -> Eql a c
trans Refl Refl = Refl


-- castWith
castWith :: Eql a b -> a -> b
castWith Refl = id


theorem1 :: forall a. Eql a a
theorem1 = Refl

theorem2 :: forall. Eql () ()
theorem2 = Refl



