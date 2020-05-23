universes u v

constant quot2 : ∀ {α : Sort u}, (α → α → Prop) → Sort u

--#check @quot2
--#check @quot

constant quot2.mk : ∀ {α : Sort u} (r : α → α → Prop), α → quot2 r

--#check @quot2.mk
--#check @quot.mk

axiom quot2.ind : ∀ {α : Sort u} {r : α → α → Prop} {β : quot2 r → Prop},
  (∀ (a:α), β (quot2.mk r a)) → ∀ (q : quot2 r), β q

--#check @quot2.ind
--#check @quot.ind

constant quot2.lift : ∀ {α : Sort u} {r : α → α → Prop} {β : Sort u} (f : α → β),
  (∀ a b, r a b → f a = f b) → quot2 r → β

--#check @quot2.lift
--#check@quot.lift


lemma lift_compute : ∀ {α : Sort u} {r : α → α → Prop} {β : Sort u} (f : α → β)
  (H:∀ a b, r a b → f a = f b) (x:α), quot.lift f H (quot.mk r x) = f x :=
begin
  intros α r β f H x, refl
end

axiom quot2.sound : ∀ {α : Type u} {r : α → α → Prop} {a b : α},
  r a b → quot2.mk r a = quot2.mk r b

--#check @quot2.sound
--#check @quot.sound




