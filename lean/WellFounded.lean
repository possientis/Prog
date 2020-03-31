universe u

def LEM   : Prop := ∀ (A:Prop), A ∨ ¬A
def IRREL : Prop := ∀ (A:Prop) (p q:A), p = q

-- Proof irrelevance is true in Lean by default, unlike Coq
lemma L1 : IRREL :=
  assume A p q,
    begin
      simp
    end

lemma L2 : IRREL := λ (A:Prop) (p:A) (q:A), rfl

inductive Accessible {α : Type u} (r : α → α → Prop) : α → Prop
| MkAcc : ∀ (x:α), (∀ (y:α), r y x → Accessible y) → Accessible x

def WellFounded {α : Type u} (r : α → α → Prop) : Prop := ∀ (x:α), Accessible r x

lemma LessThanAccIsAcc : ∀ {α : Type u} (r : α → α → Prop) (x y : α),
  r y x → Accessible r x → Accessible r y :=
  assume α r x y R Ax,
    begin
      cases Ax with x H,
      apply H, assumption
    end

open nat
open has_lt

lemma AllNatsAccessible : ∀ (n : ℕ), Accessible (<) n :=
  assume n,
    begin
      induction n with n IH; constructor,
        {from assume n H, by cases H},
        {from assume m H, begin cases decidable.em (m = n) with H' H',
              {rewrite H', assumption},
              {unfold has_lt.lt at H, unfold nat.lt at H,
               have H1 := le_of_succ_le_succ H,
               have H2 := lt_or_eq_of_le H1,
               cases H2 with H2 H2,
                 {apply LessThanAccIsAcc, exact H2, assumption},
                 {have H3 := H' H2, contradiction}
              }
        end}
    end

lemma LtWellFounded : @WellFounded ℕ (<) :=
  begin
    unfold WellFounded,
      from assume n,
        begin
          apply AllNatsAccessible
        end
  end

def Reflexive  {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (x:α), r x x

def AntiSym    {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (x y:α), r x y → r y x → x = y

def Transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (x y z:α), r x y → r y z → r x z

def Total      {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (x y:α), r x y ∨ r y x

def TotalOrder {α : Type u} (r : α → α → Prop) : Prop :=
  Reflexive r ∧ AntiSym r ∧ Transitive r ∧ Total r

def Minimal {α : Type u} (r : α → α → Prop) (x : α) : Prop :=
  ∀ (y:α), r y x → x = y.

inductive Embedding (β α : Type u) : Type u
| Embed : ∀ (j:β → α), (∀ (x y:β), j x = j y → x = y) → Embedding

open Embedding

def restrict {α β : Type u} : Embedding β α → (α → α → Prop) → (β → β → Prop)
| (Embed j _) r x y := r (j x) (j y)

-- Every non-empty subset has a minimal element
def HasMinProp {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (β:Type u) (e:Embedding β α) (y:β), -- non-empty embedding
    ∃ (z:β), Minimal (restrict e r) z

def WellOrder {α : Type u} (r : α → α → Prop) : Prop :=
  TotalOrder r ∧ HasMinProp r

-- returns a 'strict' counterpart of a given relation
def strict {α : Type u} (r : α → α → Prop) (x y : α) : Prop :=
  r x y ∧ ¬ x = y

open has_le

lemma LeReflexive : Reflexive (@le ℕ _) :=
  begin unfold Reflexive, apply le_refl, end

lemma LeAntiSym : AntiSym (@le ℕ _) :=
  begin unfold AntiSym, apply le_antisymm, end

lemma LeTransitive : Transitive (@le ℕ _) :=
  begin unfold Transitive, apply le_trans, end

lemma nat_total_order: ∀ (m n : ℕ), ¬m = n → m < n ∨ n < m :=
begin
  assume m n H,
  cases decidable.em (m <= n) with H H,
    {left, apply lt_of_le_of_ne; assumption},
    {right, apply lt_of_not_ge, assumption}
end

lemma LeTotal : Total (@le ℕ _) :=
begin
  unfold Total, assume m n,
  cases decidable.em (m = n) with H H,
    {subst m, left, apply le_refl},
    {have H := nat_total_order m n H, cases H with H H,
      {left, apply le_of_lt, assumption},
      {right, apply le_of_lt, assumption}}
end

lemma LeTotalOrder : TotalOrder (@le ℕ _) :=
begin
  unfold TotalOrder, split,
    {apply LeReflexive},
    {split,
      {apply LeAntiSym},
      {split,
        {apply LeTransitive},
        {apply LeTotal}}}
end

lemma LeHasMinProp : LEM → HasMinProp (@le ℕ _) :=
begin
  unfold HasMinProp, assume L β e x, cases e with j p,
  unfold Minimal, unfold restrict, generalize E:j x = n,
  have H:j x <= n := begin rewrite E end, clear E,
  revert H, revert p, revert x, revert j, revert β,
  induction n with n IH; assume β j x p H,
    { existsi x, assume y H', apply p,
      have H1 : j x = 0 := eq_zero_of_le_zero H,
      have H2 : j y = 0 :=
        begin
          apply eq_zero_of_le_zero, apply le_trans, apply H', assumption
        end,
      rewrite H1, rewrite H2},
    { have H' := lt_or_eq_of_le H, clear H, cases H' with H H,
        { have H' := le_of_succ_le_succ H, clear H, apply IH; assumption},
        { cases (L (∃ (y:β), j y ≤ n)) with H' H',
          { clear H, clear x, cases H' with x H, apply IH; assumption},
          { existsi x, assume y H0, have H1 : j y ≤ succ n,
            {rewrite <- H, assumption},
            have H2 := lt_or_eq_of_le H1, clear H0, clear H1, cases H2 with H0 H0,
              { have H1 := le_of_succ_le_succ H0, clear H0, exfalso,
                apply H', existsi y, assumption},
              {apply p, rewrite H0, rewrite H}}}}
end


lemma LeWellOrder : LEM → WellOrder (@le ℕ _) :=
begin
  assume L, unfold WellOrder, split,
    { apply LeTotalOrder},
    { apply LeHasMinProp, assumption }
end

def NotAccessibleType {α : Type u} (r : α → α → Prop) : Type u :=
  { x : α // ¬ Accessible r x}



def NotAccessibleInj {α : Type u} (r : α → α → Prop) : NotAccessibleType r → α :=
    subtype.val

lemma NotAccessibleInjInj : ∀ {α : Type u} (r : α → α → Prop),
  ∀ (x y : NotAccessibleType r),
       NotAccessibleInj r x = NotAccessibleInj r y → x = y :=
begin
  assume α r x y H, cases x with x p, cases y with y q,
  unfold NotAccessibleInj at H, simp at H, revert p q, rewrite H,
  assume p q, have H':p = q, {simp}, rewrite H'
end

def NotAccessibleEmbedding {α : Type u} (r : α → α → Prop)
  : Embedding (NotAccessibleType r) α := Embed
      (NotAccessibleInj r)
      (NotAccessibleInjInj r)

lemma WellOrderAllAccessible : ∀ {α : Type u} (r : α → α → Prop),
  LEM → WellOrder r → ∀ (x:α), Accessible (strict r) x :=
begin
  assume α r L H x,
  unfold WellOrder at H, unfold TotalOrder at H,
  cases H with H H5,
  cases H with H1 H,
  cases H with H2 H,
  cases H with H3 H4,
  cases (L (Accessible (strict r) x)) with H H,
    { assumption },
    { unfold HasMinProp at H5,
      generalize Eβ:NotAccessibleType (strict r) = β,
      unfold NotAccessibleType at Eβ,
      generalize Ee:NotAccessibleEmbedding (strict r) = e,
      generalize Ex:subtype.mk x H = x',
      generalize E:H5 β = H6, clear E, rewrite ← Eβ at H6, clear H5,
      generalize E:H6 e x' = H7, clear E, clear H6, clear Ex, clear x',
      clear H, exfalso, clear x, clear Eβ, clear β, cases H7 with x H,
      cases x with x p, unfold Minimal at H,
      rewrite ← Ee at H, unfold NotAccessibleEmbedding at H,
      unfold NotAccessibleInj at H, apply p, constructor,
      assume y Hy, cases (L (Accessible (strict r) y)) with H' H',
        { assumption },
        { generalize Ey:subtype.mk y H' = y',
          generalize E:(H y') = H5, clear E,
          rewrite ← Ey at H5, simp at H5, clear H, unfold strict at Hy,
          cases Hy with H6 H7, clear Ee, clear e,
          generalize E:H5 H6 = H8, clear E, clear H5, clear Ey, clear y', clear H6,
          exfalso, apply H7, rewrite H8
        }
    }
end

-- If r is a well-order, then (strict r) is well-founded
theorem WellOrderWF : ∀ {α : Type u} (r : α → α → Prop),
  LEM → WellOrder r → WellFounded (strict r) :=
begin
  assume α r L H, unfold WellFounded, apply WellOrderAllAccessible; assumption
end

-- acc is defined by Lean
lemma acc_Accessible : ∀ {α : Type u} (r : α → α → Prop) (x : α),
  Accessible r x ↔ acc r x :=
begin
  assume α r x, split; assume H,
    { induction H with x H IH, constructor, assume y H', apply IH, assumption},
    { induction H with x H IH, constructor, assume y H', apply IH, assumption}
end

-- well_founded is defined by Lean
lemma well_founded_WellFounded: ∀ {α : Type u} (r : α → α → Prop),
  WellFounded r ↔ well_founded r :=
begin
  assume α r, split; assume H,
    { constructor, assume x, rewrite ← acc_Accessible, apply H},
    { unfold WellFounded, assume x, rewrite acc_Accessible, cases H with H, apply H}
end


def AccessibleInv2 : ∀ {α : Type u} (r : α → α → Prop) (x : α),
  Accessible r x → ∀ (y : α), r y x → Accessible r y :=
begin
  assume α r x H, cases H, assumption
end

-- same as Coq pretty much
def AccessibleInv : ∀ {α : Type u} (r : α → α → Prop) (x : α),
  Accessible r x → ∀ (y:α), r y x → Accessible r y :=
    λ (α : Type u),
      λ (r : α → α → Prop),
        λ (x : α),
          λ (p : Accessible r x),
            match p with
            | ⟨_,q⟩ := q
            end

#check @well_founded.fix -- counterpart of Fix in Coq

/-
-- The primitive 'fix' does not seem to exist in Lean.
def WFRecursion_F : ∀ {α : Type u} (r : α → α → Prop) (c : α → Type u),
  (∀ (x:α), (∀ (y:α), r y x → c y) → c x) →
   ∀ (x:α), Accessible r x → c x :=
     λ (α:Type u),
       λ (r:α → α → Prop),
         λ (c:α → Type u),
           λ (IH:∀ (x:α), (∀(y:α), r y x → c y) → c x),
             λ (x : α),
               λ (p:Accessible r x),
                 IH x (λ (y:α),
                   λ (H:r y x), _)
-/


def fac : ∀ (α : Type u), ℕ → ℕ
| α 0 := 1
| α (succ n) := succ n * fac α n

/- This won't work either
def WFRecursion_F : ∀ (α : Type u) (r : α → α → Prop) (c : α → Type u),
  (∀ (x:α), (∀ (y:α), r y x → c y) → c x) →
  ∀ (x:α), Accessible r x → c x
| α r c IH x (Accessible.MkAcc _ f) :=
  IH x (λ (y:α) (H:r y x), WFRecursion_F α r c IH y (f y H))
-/
