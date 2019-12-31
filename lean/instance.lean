variable {α : Type}

def isPrefix (xs : list α) (ys : list α) : Prop :=
  ∃ (t : list α), xs ++ t = ys

instance list_has_le : has_le (list α) := ⟨isPrefix⟩

lemma list.isPrefixRelf : ∀ (xs : list α), xs ≤ xs :=
  assume xs, ⟨[], by simp⟩

section
local attribute [instance] list_has_le

lemma foo (xs : list α): xs ≤ xs := ⟨[], by simp⟩
end


