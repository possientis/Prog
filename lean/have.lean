variable f : ℕ → ℕ
variable H : ∀ (n:ℕ), f n ≤ f (n+1)


example : f 0 ≤ f 3 :=
  have f 0 ≤ f 1, from H 0,
  have f 0 ≤ f 2, from le_trans this (H 1) ,
  show f 0 ≤ f 3, from le_trans this (H 2)

example : f 0 ≤ f 3 :=
  have f 0 ≤ f 1, from H 0,
  have f 0 ≤ f 2, from le_trans (by assumption) (H 1),
  show f 0 ≤ f 3, from le_trans (by assumption) (H 2)

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  assume : f 1 ≤ f 0,
  assume : f 2 ≤ f 1,
  show f 0 = f 2, from
  have f 2 ≤ f 0, from le_trans this ‹f 1 ≤ f 0›, -- \f< and \f>
  have f 0 ≤ f 2, from le_trans (H 0) (H 1),
  show f 0 = f 2, from
  le_antisymm ‹f 0 ≤ f 2› ‹f 2 ≤ f 0›                    -- \f< and \f>

example : f 0 ≤ f 3 :=
  have f 0 ≤ f 1, from H 0,
  have f 1 ≤ f 2, from H 1,
  have f 2 ≤ f 3, from H 2,
  show f 0 ≤ f 3, from
    le_trans ‹f 0 ≤ f 1› (le_trans ‹f 1 ≤ f 2› ‹f 2 ≤ f 3›)
