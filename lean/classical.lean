open classical

variable p : Prop

----#check em p -- law of excluded middle

-- This requres law of exlcuded middle
lemma L1 : ∀ (p:Prop), ¬¬p → p := λ p h,
  or.elim (em p)
    (assume hp : p, hp)
    (assume hnp : ¬p, absurd hnp h)


----#check L1


lemma L2 : ∀ (p:Prop), ¬¬p → p := λ p h,
  by_cases
    (assume h1:p, h1)
    (assume h1:¬p, absurd h1 h)

----#check L2


lemma L3 : ∀ (p:Prop), ¬¬p → p := λ p h,
  by_contradiction
    (assume h1:¬p,
      show false, from h h1)

----#check L3


lemma L4 : ∀ (p q:Prop), ¬(p ∧ q) → ¬p ∨ ¬q := λ p q h,
  or.elim (em p) -- p ∨ ¬p
    (assume hp:p, or.inr
      (show ¬q, from
        (assume hq:q, h ⟨hp,hq⟩)))
    (assume hp:¬p, or.inl
      (show ¬p, from
        hp))

--#check L4


lemma L5 : ∀ (p q:Prop), ¬(p ∧ q) → ¬p ∨ ¬q := λ p q h,
  or.elim (em p)
    (assume hp: p, or.inr
      (show ¬q, from
        (assume hq:q, h ⟨hp,hq⟩)))
    (assume hp:¬p, or.inl hp)

--#check L5


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

--#check L7

-- not readable
lemma L8 : ∀ (α:Type) (p:α → Prop), (¬∀ (x:α), ¬p x) → ∃ (x:α), p x :=
assume α p H, by_contradiction
  (assume H', H (assume x P, (H' ⟨x,P⟩)))

--#check L8

-- is this better ?
lemma L9 : ∀ (α:Type) (p:α → Prop), (¬∀ (x:α), ¬p x) → ∃ (x:α), p x :=
  assume α p (H : ¬∀ x, ¬p x), by_contradiction
    (assume H' : ¬∃ x, p x, show false,
      from H (show ∀ x, ¬p x,
        from assume x (P : p x), show false,
          from H' (show ∃ x, p x,
            from ⟨x,P⟩)))
--#check L9

-- constructive
lemma L10 : ∀ (α:Type) (r:Prop), (∃ (x:α), r) -> r :=
  assume α r ⟨x,H⟩, show r,
    from H

--#check L10

lemma L11 : ∀ (α:Type) (a:α) (r:Prop), r → (∃ (x:α), r) :=
  assume α a r (p:r), show ∃ (x:α), r ,
    from ⟨a,p⟩

--#check L11


lemma L12 : ∀ (α:Type) (r:Prop) (p:α → Prop), (∃x,p x ∧ r) ↔ (∃x,p x) ∧ r :=
  assume α r p, ⟨
    assume ⟨x,⟨H1,H2⟩⟩,
      show (∃x,p x) ∧ r,
        from ⟨⟨x,H1⟩,H2⟩
  , assume ⟨⟨x,H1⟩,H2⟩,
      show ∃x, (p x ∧ r),
        from ⟨x, ⟨H1,H2⟩⟩⟩

--#check L12

lemma L13 : ∀ (α:Type) (p q:α → Prop),
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

--#check L13

lemma L14 : ∀ (α:Type) (p:α → Prop),
  (∀ (x:α), p x) ↔ ¬ (∃ (x:α), ¬ p x) :=
  assume α p, ⟨
    assume H ⟨x,H'⟩, (H' (H x))
  ,
    assume H' x, show p x, from
      or.elim (em (p x))
        (assume H, H)
        (assume H, false.elim
          (H' ⟨x,H⟩))⟩

--#check L14

lemma L15 : ∀ (α:Type) (p:α → Prop),
  (∃ (x:α), p x) ↔ ¬ (∀ (x:α), ¬ p x) :=
  assume α p, ⟨
    assume ⟨x,H⟩,
      assume H':∀ x, ¬p x, show false, from
        ((H' x) H)
  ,
    assume H:¬∀x, ¬p x, by_contradiction (
      assume H', show false, from (H
        (assume x P, show false, from
          H' ⟨x,P⟩)))⟩

--#check L15


lemma L16 : ∀ (α:Type) (p:α → Prop),
  ¬(∃ (x:α), p x) ↔ (∀ (x:α), ¬ p x) :=
  assume α p, ⟨
    assume H x H', H ⟨x,H'⟩
  ,
    assume H ⟨x,H'⟩, (H x) H'⟩

--#check L16

lemma L17 : ∀ (α:Type) (p:α → Prop),
  ¬(∀ (x:α), p x) ↔ (∃ (x:α), ¬ p x) :=
  assume α p, ⟨
    assume H, by_contradiction (
      assume H', H (
        (assume x, by_contradiction
          (assume P, H' ⟨x, P⟩))))
  ,
  assume ⟨x,H⟩ H', H (H' x)⟩

--#check L17


lemma L18 : ∀ (α:Type) (p:α → Prop) (r:Prop),
  (∀ (x:α), p x → r) ↔ (∃ (x:α), p x) → r :=
  assume α p r, ⟨
    assume H ⟨x,H'⟩, (H x) H'
  ,
    assume H x H', H ⟨x,H'⟩⟩

--#check L18

--#check @by_cases

lemma L19 : ∀ (α:Type) (p:α → Prop) (r:Prop) (a:α), -- type α is not void !!!
  (∃ (x:α), p x → r) ↔ (∀ (x:α), p x) → r :=
  assume α p r a, ⟨
    assume ⟨x,H⟩ H', H (H' x),
    assume H, or.elim (em (∀ x, p x))
      (assume H', ⟨a, assume P, H H'⟩)  -- need 'a' here
      (assume H', by_contradiction
        (assume H'', H'
          (assume x, by_contradiction
            (assume P, H'' ⟨x,
              (assume Q, false.elim (P Q))⟩))))⟩

--#check L19

lemma L20 : ∀ (α:Type) (p:α → Prop) (r:Prop) (a:α),  -- type α is not void !!!
  (∃ (x:α), r → p x) ↔ (r → ∃ (x:α), p x) :=
  assume α p r a, ⟨
    assume ⟨x,H⟩ R, ⟨x, H R⟩
  ,
    assume H, or.elim (em r)
      (assume R,
        (have H' : ∃ x, p x, from H R,
          exists.elim H'
            (assume b P, ⟨b, assume _, P⟩)))
      (assume R, ⟨a, assume R', false.elim (R R')⟩)⟩

--#check L20


lemma L21 : ∀ (α:Type) (p q:α → Prop),
  (∀ (x:α), p x ∧ q x) ↔ (∀ (x:α), p x) ∧ (∀ (x:α), q x) :=
  assume α p q,
  ⟨ -- =>
    assume H : ∀ (x:α), p x ∧ q x,
      ⟨show ∀ (x:α), p x, from
        assume x, show p x, from (and.left (H x))
      ,
      show ∀ (x:α), q x, from
        assume x, show q x, from (and.right (H x))
      ⟩
  , -- <=
    assume ⟨H1,H2⟩, show ∀ (x:α), p x ∧ q x, from
      assume x, ⟨H1 x, H2 x⟩
  ⟩

--#check L21


lemma L22 : ∀ (α:Type) (p q:α → Prop),
  (∀ (x:α), p x → q x) → (∀ (x:α), p x) → (∀ (x:α), q x) :=
  assume α p q (H1 : ∀ x, p x → q x) (H2 : ∀ x, p x),
    show ∀ x, q x, from
      assume x, (H1 x) (H2 x)

--#check L22

lemma L23 : ∀ (α:Type) (p q:α → Prop),
  (∀ (x:α), p x) ∨ (∀ (x:α), q x) → ∀ (x:α), p x ∨ q x :=
  assume α p q H, or.elim H
    (assume H1 x, or.intro_left  _ (H1 x))
    (assume H1 x, or.intro_right _ (H1 x))

--#check L23

lemma L24 : ∀ (α:Type) (p q:α → Prop) (r:Prop) (a:α),
  (∀ (x:α), r) ↔ r :=
  assume α p q r a,
  ⟨
    assume H, H a
  ,
    assume H _, H
  ⟩

--#check L24

lemma L25 : ∀ (α:Type) (p:α → Prop) (r:Prop),
  (∀ (x:α), p x ∨ r) ↔ (∀ (x:α), p x) ∨ r :=
  assume α p r,
  ⟨ show (∀ (x:α), p x ∨ r) → (∀ (x:α), p x) ∨ r, from
    assume H:∀ x, p x ∨ r,
    show (∀ (x:α), p x) ∨ r, from
    or.elim (em r)
      (assume R:r, or.intro_right _ R)
      (assume nonR:¬r, or.intro_left _
        (show ∀ (x:α), p x, from
          assume x:α, show p x, from
            or.elim (H x)
              (assume : p x, this)
              (assume : r, false.elim (nonR this))))
  ,
  show (∀ (x:α),p x) ∨ r → ∀ (x:α), p x ∨ r, from
  assume H:(∀ (x:α), p x) ∨ r,
  show ∀ (x:α), p x ∨ r, from
  or.elim H
    (assume : ∀ (x:α), p x, show ∀ (x:α), p x ∨ r, from
      assume (x:α), show p x ∨ r, from
        or.intro_left _ (this x))
    (assume R:r, show ∀ (x:α), p x ∨ r, from
      assume (x:α), show p x ∨ r, from
        or.intro_right _ R)
  ⟩

lemma L26 : ∀ (α:Type) (p:α → Prop) (r:Prop),
  (∀ (x:α), r → p x) ↔ (r → ∀ (x:α), p x) :=
  assume α p r,
  ⟨
    assume H R x, H x R
  ,
    assume H x R, H R x
  ⟩


--#check L26
