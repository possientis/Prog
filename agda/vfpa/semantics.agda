open import formula
open import kripke

open Kripke

-- Expressing 'truth' of a formula in a world w of some Kripke structure k
_,_⊨_ : (k : Kripke) → W k → Formula → Set
k , w ⊨ p = {!!} 
