
lemma L1 : ∀ (p q:Prop), p → q → p ∧ q :=
  λ p q hp hq, and.intro hp hq

lemma L2 : ∀ (p q:Prop), p ∧ q → p :=
  λ p q h, and.elim_left h

lemma L2' : ∀ (p q:Prop), p ∧ q → p :=
  λ p q h, and.left h

lemma L3 : ∀ (p q:Prop), p ∧ q → q :=
  λ p q h, and.elim_right h

lemma L3' : ∀ (p q:Prop), p ∧ q → q :=
  λ p q h, and.right h

lemma L4 : ∀ (p q:Prop), p ∧ q → q ∧ p :=
  λ p q h, and.intro (and.right h) (and.left h)

lemma L4' : ∀ (p q:Prop), p ∧ q → q ∧ p :=
  λ p q h, ⟨(and.right h),(and.left h)⟩   -- \langle, \rangle, or \< \>

lemma L4'' : ∀ (p q:Prop), p ∧ q → q ∧ p :=
  λ p q h, (|(and.right h),(and.left h)|) 


#check L1
#check L2
#check L2'
#check L3
#check L3'
#check L4
#check L4'
#check L4''

variable l : list ℕ

#check list.head l
#check l.head

lemma L5 : ∀ (p q:Prop), p ∧ q → q ∧ p :=
  λ p q h, ⟨h.right,h.left⟩

#check L5

lemma L6 : ∀ (p q:Prop), p ∧ q → q ∧ p ∧ q :=
  λ p q h, ⟨h.right,⟨h.left,h.right⟩⟩
#check L6




