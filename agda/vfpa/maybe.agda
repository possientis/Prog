module maybe where

data maybe {ℓ} (a : Set ℓ) : Set ℓ where
  just    : a → maybe a
  nothing : maybe a
