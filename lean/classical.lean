open classical

variable p : Prop

#check em p -- law of excluded middle

-- This requres law of exlcuded middle
lemma L1 : ∀ (p:Prop), ¬¬p → p := λ p h,
  or.elim (em p)
    (assume hp : p, hp)
    (assume hnp : ¬p, absurd hnp h)


#check L1


lemma L2 : ∀ (p:Prop), ¬¬p → p := λ p h,
  by_cases
    (assume h1:p, h1)
    (assume h1:¬p, absurd h1 h)

#check L2


lemma L3 : ∀ (p:Prop), ¬¬p → p := λ p h,
  by_contradiction
    (assume h1:¬p,
      show false, from h h1)

#check L3


lemma L4 : ∀ (p q:Prop), ¬(p ∧ q) → ¬p ∨ ¬q := λ p q h,
  or.elim (em p) -- p ∨ ¬p
    (assume hp:p, or.inr
      (show ¬q, from
        (assume hq:q, h ⟨hp,hq⟩)))
    (assume hp:¬p, or.inl
      (show ¬p, from
        hp))

#check L4


lemma L5 : ∀ (p q:Prop), ¬(p ∧ q) → ¬p ∨ ¬q := λ p q h,
  or.elim (em p)
    (assume hp: p, or.inr
      (show ¬q, from
        (assume hq:q, h ⟨hp,hq⟩)))
    (assume hp:¬p, or.inl hp)

#check L5


lemma L6 : ∀ (p q:Prop), ¬(p ∧ q) → ¬p ∨ ¬q := λ p q h,
 or.elim (em p)
   (assume hp:p,
     or.inr (assume hq:q, (h ⟨hp,hq⟩)))
   (assume hp:¬p,
     or.inl hp)

lemma L7 : ∀ (p q r:Prop), p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := λ p q r,
  iff.intro
  (assume h : p ∧ (q ∨ r),
    (show p ∧ q ∨ p ∧ r, from
      (have hp:p, from and.left h,
        (have hqr:q∨r, from and.right h,
          (or.elim hqr
            (assume hq:q, or.inl ⟨hp,hq⟩)
            (assume hr:r, or.inr ⟨hp,hr⟩))))))
  (assume h: p ∧ q ∨ p ∧ r, or.elim h
    (assume hpq:p ∧ q,
      (have hp:p, from and.left hpq,
        (have hq:q, from and.right hpq,
          ⟨hp,or.inl hq⟩)))
    (assume hpr:p ∧ r,
      (have hp:p, from and.left hpr,
        (have hr:r, from and.right hpr,
          ⟨hp,or.inr hr⟩))))

#check L7

-- not readable
lemma L8 : ∀ (α:Type) (p:α → Prop), (¬∀ (x:α), ¬p x) → ∃ (x:α), p x :=
assume α p H, by_contradiction
  (assume H', H (assume x P, (H' ⟨x,P⟩)))

#check L8

-- is this better ?
lemma L9 : ∀ (α:Type) (p:α → Prop), (¬∀ (x:α), ¬p x) → ∃ (x:α), p x :=
  assume α p (H : ¬∀ x, ¬p x), by_contradiction
    (assume H' : ¬∃ x, p x, show false,
      from H (show ∀ x, ¬p x,
        from assume x (P : p x), show false,
          from H' (show ∃ x, p x,
            from ⟨x,P⟩)))
#check L9

-- constructive
lemma L10 : ∀ (α:Type) (r:Prop), (∃ (x:α), r) -> r :=
  assume α r ⟨x,H⟩, show r,
    from H

#check L10

lemma L11 : ∀ (α:Type) (a:α) (r:Prop), r → (∃ (x:α), r) :=
  assume α a r (p:r), show ∃ (x:α), r ,
    from ⟨a,p⟩

#check L11


lemma L12 : ∀ (α:Type) (r:Prop) (p:α → Prop), (∃x,p x ∧ r) ↔ (∃x,p x) ∧ r :=
  assume α r p, ⟨
    assume ⟨x,⟨H1,H2⟩⟩,
      show (∃x,p x) ∧ r,
        from ⟨⟨x,H1⟩,H2⟩
  , assume ⟨⟨x,H1⟩,H2⟩,
      show ∃x, (p x ∧ r),
        from ⟨x, ⟨H1,H2⟩⟩⟩

#check L12

lemma L13 : ∀(α:Type) (p q:α → Prop),
  (∃ (x:α), p x ∨ q x) ↔ (∃ (x:α), p x) ∨ (∃ (x:α), q x) :=
  assume α p q, ⟨
    assume ⟨x,H⟩, (
      or.elim H
        (assume (H:p x), or.intro_left _ ⟨x,H⟩)
        (assume (H:q x), or.intro_right _ ⟨x,H⟩))
    ,
    assume H, (
      or.elim H
        (assume ⟨x,H'⟩, ⟨x,or.intro_left _ H'⟩)
        (assume ⟨x,H'⟩, ⟨x,or.intro_right _ H'⟩))⟩

#check L13
