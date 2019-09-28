data Comb : Set where
  S   : Comb
  K   : Comb
  App : Comb → Comb → Comb

data Small : Comb → Comb → Set where
  KSmall : (a b : Comb) → Small (App (App K a) b) a
  SSmall : (a b c : Comb) → Small (App (App (App S a) b) c) (App (App a c) (App b c))
  Cong1  : {a a' : Comb} →  (b : Comb) → Small a a' → Small (App a b) (App a' b)
  Cong2  : {b b' : Comb} →  (a : Comb) → Small b b' → Small (App a b) (App a b')


