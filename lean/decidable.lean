namespace hidden

class inductive decidable (p : Prop) : Type
| is_false : ¬p → decidable
| is_true  :  p → decidable

-- if-then-else
def ite (p : Prop) [d : decidable p] {α : Type} (t e : α) : α :=
  decidable.rec_on d (λ _, e) (λ _, t)

-- dependent version
def dite (p : Prop) [d : decidable p] {α : Type} (t : p → α) (e : ¬p → α) : α :=
  decidable.rec_on d e t

end hidden

#check @and.decidable
#check @or.decidable
#check @not.decidable
#check @implies.decidable

open nat
def step (a b x : ℕ) : ℕ :=
  if x < a ∨ x > b then 0 else 1

set_option pp.implicit true
#print definition step

open classical
local attribute [instance] prop_decidable


