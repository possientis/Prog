universes u v

axiom funext2 : ∀ {α : Sort u} {β : α → Sort v} {f g : ∀ (x:α), β x},
  (∀ (x:α), f x = g x) → f = g

--#check @funext2
--#check @funext


lemma L1 : Prop = Sort 0 := rfl
lemma L2 : Type u = Sort (u + 1) := rfl


def f₁ (x : ℕ) := x
def f₂ (x : ℕ) := 0 + x

lemma feq : f₁ = f₂ :=
begin
  apply funext, intros x, symmetry, apply zero_add
end

def val1 : ℕ := eq.rec_on feq (0 : ℕ)

-- #check @ eq.rec_on

-- complicated !
-- #reduce val1

-- evaluates to 0
-- #eval val1

lemma tteq : (true ∧ true) = true :=
begin
  apply propext, split,
    {intros H, cases H with H1 H2, assumption},
    {intros H, split; assumption}
end

def val2 : ℕ := eq.rec_on tteq 0

-- complicated !
-- #reduce val2

-- evaluates to 0
-- #eval val2

