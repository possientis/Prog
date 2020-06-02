universe u

class inductive nonempty2 (α : Sort u) : Prop
| intro : α → nonempty2


--#check @nonempty
--#check @nonempty2

lemma L1 : ∀ {α : Type u}, nonempty α ↔ ∃ (x:α), true :=
begin
  intros α, split; intros H; cases H with x,
    {existsi x, constructor},
    {constructor, exact x}
end

axiom choice2 {α : Sort u} : nonempty α → α

--#check @choice2
--open classical
--#check @choice

noncomputable theorem indefinite_description2 {α : Sort u} (p : α → Prop) : (∃ x, p x) → {x // p x} :=
begin
  intros H, apply classical.choice,
  cases H with x H /- now possible -/, constructor, constructor, exact H
end

noncomputable def some2 {α : Sort u} {p : α → Prop} (H:∃ x, p x) : α :=
  subtype.val (classical.indefinite_description p H)

theorem some_spec {α : Sort u} {p : α → Prop} (H: ∃ x, p x) : p (classical.some H) :=
  subtype.property (classical.indefinite_description p H)


noncomputable theorem inhabited_of_nonempty {α : Type u} : nonempty α → inhabited α :=
begin
  intros H, apply classical.choice,
  cases H with x /- now possible -/, constructor, constructor, exact x
end

--#check @classical.strong_indefinite_description
--#check @classical.epsilon

