variable {α : Type*}

def isPrefix (xs : list α) (ys : list α) : Prop :=
  ∃ (t : list α), xs ++ t = ys

--#check @isPrefix
--#print isPrefix

infix ` <+: `:50 := isPrefix

attribute [simp]
lemma list.isPrefixRefl : ∀ (xs : list α), xs <+: xs :=
  assume xs, ⟨[], by simp⟩

lemma L1 : [1,2,3] <+: [1,2,3] := by simp

--#check @list.isPrefixRefl

--#check L1

@[simp]
lemma list.isPrefixRefl' : ∀ (xs : list α), xs <+: xs :=
  assume xs, ⟨[], by simp⟩


--#check @list.isPrefixRefl'

lemma list.isPrefixRefl3 : ∀ (xs : list α), xs <+: xs :=
  assume xs, ⟨[], by simp⟩

attribute [simp] list.isPrefixRefl3

local attribute [simp]
lemma list.isPrefixRefl4 : ∀ (xs : list α), xs <+: xs :=
  assume xs, ⟨[], by simp⟩

