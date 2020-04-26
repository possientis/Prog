--#check eq.refl
--#check eq.symm
--#check eq.trans

namespace hidden

universe u

--#check @eq.refl.{u}
--#check @eq.symm.{u}
--#check @eq.trans.{u}


lemma L1 : 2 + 3 = 5 :=
  eq.refl _

--#check L1

lemma L2 : 2 + 3 = 5 := rfl

--#check L2

lemma L3 : ∀ (α : Type u) (a b : α)(p : α → Prop), a = b → p a → p b
:= assume α a b p q H, eq.subst q H

--#check L3

lemma L4 : ∀ (α : Type u) (a b : α)(p : α → Prop), a = b → p a → p b
:= assume α a b p q H, q ▸ H -- \t

--#check L4

lemma cong : ∀ {α β : Type u} {x y : α} (f : α → β), x = y → f x = f y
:= assume α β x y f p, p ▸ rfl

--#check @cong


lemma L5 : ∀ {α β : Type u} {f g : α → β} (x : α) , f = g → f x = g x :=
begin
  intros α β f g x p, rw p
end

--#check L5

lemma L6 : ∀ {α β : Type u} {f g : α → β} (x y : α), f = g → x = y → f x = g y :=
begin
  intros α β f g x y H1 H2, rw H1, rw H2
end

--#check L6

--#check @congr_arg -- same as cong
--#check @congr_fun
--#check @congr

--#check @add_zero
--#check @zero_add 
--#check @mul_one
--#check @one_mul
--#check @neg_add_self
--#check @add_neg_self
--#check @sub_self
--#check @add_comm
--#check @add_assoc
--#check @mul_comm
--#check @mul_assoc
--#check @mul_add
--#check @left_distrib
--#check @add_mul
--#check @right_distrib
--#check @mul_sub
--#check @sub_mul


lemma L7 : forall (x y z : ℤ), x * (y + z) = x * y + x * z
:= assume x y z, mul_add x y z

--#check L7

end hidden











