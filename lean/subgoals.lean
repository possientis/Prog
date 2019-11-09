 lemma L1 : ∀ (p q:Prop), p ∧ q → q ∧ p := λ p q h,
   have hp : p, from and.left h,
   have hq : q, from and.right h,
   show q ∧ p, from and.intro hq hp


 lemma L1' : ∀ (p q:Prop), p ∧ q → q ∧ p := λ p q h,
   have hp : p, from and.left h,
   suffices hq :q, from and.intro hq hp,
   show q, from and.right h


#check L1
#check L1'
