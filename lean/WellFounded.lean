universe u

def LEM   : Prop := ∀ (A:Prop), A ∨ ¬A
def IRREL : Prop := ∀ (A:Prop) (p q:A), p = q

-- Proof irrelevance is true in lean by default, unlike Coq
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


lemma AccessibleInv' : ∀ (α : Type u) (r : α → α → Prop) (x : α),
  Accessible r x -> ∀ (y:α), r y x -> Accessible r y :=
    assume a r x H,
      begin
        cases H with x H,
        assumption
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
    {existsi x, assume y H', apply p, }, -- j x <= 0 -> j x = 0 ...
    {}
end
