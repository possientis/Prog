universes u v

axiom funext2 : ∀ {α : Sort u} {β : α → Sort v} {f g : ∀ (x:α), β x},
  (∀ (x:α), f x = g x) → f = g

--#check @funext2
--#check @funext


lemma L1 : Prop = Sort 0 := rfl
lemma L2 : Type u = Sort (u + 1) := rfl
