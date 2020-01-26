universe u

open nat

inductive Vec (α : Type u) : ℕ → Type u
| nil {} : Vec 0
| cons {n : ℕ} (x : α) (xs : Vec n) : Vec (succ n)


inductive eq' (α : Sort u) (a : α) : α → Prop
| refl : eq' a

#check @eq.rec_on
#check @eq.rec

lemma L1 : ∀ (α : Type u) (a b : α) (p : α → Prop), a = b → p a → p b :=
  λ α a b p E H, eq.rec_on E H

#check L1

definition subst {α : Type u} {a b : α} (p : α → Prop)(E : a = b) (H:p a) : p b :=
  eq.rec_on E H

#check @subst

-- TODO
definition symm {α : Type u} {a b : α} (E : a = b) : b = a :=
  subst (λ (x:α), x = a) E (eq.refl a)
