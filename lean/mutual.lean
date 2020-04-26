mutual inductive even, odd
with even : ℕ → Prop
| even_zero : even 0
| even_succ : ∀ n, odd n → even (n + 1)
with odd : ℕ → Prop
| odd_succ : ∀ n, even n → odd (n + 1)


open even odd

lemma not_odd_zero : ¬ odd 0 :=
begin
  intro H, cases H
end

mutual lemma even_of_odd_succ, odd_of_even_succ
with even_of_odd_succ : ∀ (n:ℕ), odd (n + 1) → even n
| _ (odd_succ _ ne) := ne
with odd_of_even_succ : ∀ (n:ℕ), even (n + 1) → odd n
| _ (even_succ _ no) := no


universe u

namespace hidden

mutual inductive tree, list_tree (α : Type u)
with tree : Type u
| node : α → list_tree → tree
with list_tree : Type u
| nil {} : list_tree
| cons : tree → list_tree → list_tree

open list_tree

--#check @nil

end hidden

-- nested inductive type, 'tree' appears inside the 'list' type constructor
inductive tree (α : Type u)
| mk : α → list tree → tree


-- mutually recursive definitions of functions
mutual def beven, bodd
with beven : ℕ → bool
| 0       := tt
| (n + 1) := bodd n
with bodd : ℕ → bool
| 0       := ff
| (n + 1) := beven n

example (n : ℕ) : beven (n + 1) = bodd n  := by simp [beven]
example (n : ℕ) : bodd  (n + 1) = beven n := by simp [bodd]

lemma even_eq_not_odd : ∀ (n:ℕ), beven n = bnot (bodd n) :=
begin
  intro n, induction n with n IH,
    { simp [bodd, beven] },
    { simp [beven, bodd], rewrite IH, simp}
end

inductive Term
| Const : string → Term
| App   : string → list Term → Term

open Term

mutual def numConsts, numConstsLst
with numConsts : Term → ℕ
| (Const _)  := 1
| (App _ ts) := numConstsLst ts
with numConstsLst : list Term → ℕ
| [] := 0
| (t :: ts) := numConsts t + numConstsLst ts

def ex1 : Term := App "f" [App "g" [Const "x"], Const "y"]

--#eval numConsts ex1


