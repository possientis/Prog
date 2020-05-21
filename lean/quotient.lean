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




