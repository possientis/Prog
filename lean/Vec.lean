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
#check@eq.refl

definition P {α : Type u} (a : α) (x : α) : Prop := x = a

definition symm2 {α : Type u} {a b : α} (E:a = b) : b = a :=
@subst α a b (λ (x:α), x = a) E (eq.refl a)

definition trans2 {α : Type u} (a b c : α) (Eab : a = b) (Ebc : b = c) : a = c :=
  @subst α b c (λ x, a = x) Ebc Eab

definition congr2 {α β : Type u} {a b : α} (f : α → β) (E : a = b) : f a = f b :=
  @subst α a b (λ x, f a = f x) E (eq.refl (f a))
