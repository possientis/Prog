universe u

-- Type of subsets of α. A subset of α is a predicate over α
def set2 (α : Type u) : Type u := α → Prop

--#check @set2
--#check @set

variable α : Type u

def elem (x:α) (a : set α) := a x
notation e ∈ a := elem e a

lemma setext : ∀ {a b : set α}, (∀ (x:α), x ∈ a ↔ x ∈ b) → a = b :=
begin
  intros a b H, apply funext, intros x, apply propext, apply H
end

definition empty2 : set α := λ_, false

--#check @empty2
--#check @empty

--notation ∅ := empty2

def inter (a b : set α) : set α := λ x, x ∈ a ∧ x ∈ b
notation a ∩ b := inter a b


lemma inter_self : ∀ (a : set α), a ∩ a = a :=
begin
  intros a, apply funext, intros x, apply propext, split,
    {intros H, cases H with H1 H2, assumption},
    {intros H, split; assumption}
end

lemma inter_empty : ∀ (a : set α), a ∩ ∅ = ∅ :=
begin
  intros a, apply funext, intros x, apply propext, split,
    {intros H, cases H with H1 H2, assumption},
    {intros H, split,
      {exfalso, assumption},
      {assumption}}
end

lemma empty_lemma : ∀ (a : set α), ∅ ∩ a = ∅ :=
begin
  intros a, apply funext, intros x, apply propext, split,
    {intros H, cases H with H1 H2, assumption},
    {intros H, split,
      {assumption},
      {exfalso, assumption}}
end

lemma inter_comm : ∀ (a b : set α), a ∩ b = b ∩ a :=
begin
  intros a b, apply funext, intros x, apply propext, split;
    intros H; cases H with H1 H2; split; assumption
end



