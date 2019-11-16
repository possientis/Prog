#check eq.refl
#check eq.symm
#check eq.trans

universe u

#check @eq.refl.{u}
#check @eq.symm.{u}
#check @eq.trans.{u}


lemma L1 : 2 + 3 = 5 :=
  eq.refl _

#check L1

lemma L2 : 2 + 3 = 5 := rfl

#check L2

lemma L3 : ∀ (α : Type u) (a b : α)(p : α → Prop), a = b → p a → p b
:= assume α a b p q H, eq.subst q H

#check L3

lemma L4 : ∀ (α : Type u) (a b : α)(p : α → Prop), a = b → p a → p b
:= assume α a b p q H, q ▸ H -- \t

#check L4
