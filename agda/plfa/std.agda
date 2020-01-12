open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  ( +-assoc
  ; +-suc
  ; +-comm
  ; ≤-refl     -- \<=, \le
  ; ≤-trans
  ; ≤-antisym
  ; ≤-total
  )

-- +-identity... cannot type superscript r with \^r, is this due to lean ?

