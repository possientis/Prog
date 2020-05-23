universe u

class setoid2 (α : Sort u) : Sort (max 1 u) :=
  (r : α → α → Prop) (iseqv : equivalence r)

infix `≡` := setoid.r

#check @setoid
#check @setoid2

variable {α : Type u}
variable [s : setoid α]
include s


lemma L1 : ∀ (a : α), a ≡ a := (@setoid.iseqv α s).left
lemma L2 : ∀ (a b : α), a ≡ b → b ≡ a := (@setoid.iseqv α s).right.left
lemma L3 : ∀ (a b c : α), a ≡ b → b ≡ c → a ≡ c := (@setoid.iseqv α s).right.right

#check (@setoid.iseqv α s).left
