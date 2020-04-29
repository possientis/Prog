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

--#check @and.decidable
--#check @or.decidable
--#check @not.decidable
--#check @implies.decidable

open nat
def step (a b x : ℕ) : ℕ :=
  if x < a ∨ x > b then 0 else 1

set_option pp.implicit true
--#print definition step


-- Every proposition is decidable
-- priority 0 use prop_decidable as a last resort
open classical
local attribute [instance, priority 0] prop_decidable


def as_true2 (c:Prop) [decidable c] : Prop :=
if c then true else false


def of_as_true2 {c : Prop} [H1 : decidable c] (H2 : as_true c) : c :=
  match H1, H2 with
  | (is_true H), H2 := H
  | (is_false H), H2 := false.elim H2
  end

notation `dec_trivial2` := of_as_true2 (by tactic.triv)

example : 0 ≠ 1 ∧ (5 < 2 ∨ 3 < 7) := dec_trivial2


