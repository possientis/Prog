import Stmt
import Subst
import BigStep

open Stmt

def Hoare (p:Pred)(e:Stmt)(q:Pred)  : Prop :=
  ∀ (s t:Env), p s → BigStep e s t → q t


lemma skip_intro : ∀ (p:Pred), Hoare p skip p :=
begin
  intros p s t H1 H2, cases H2, assumption
end

lemma assign_intro : ∀ (p:Pred) (x:string) (a:AExp),
  Hoare (subst x a p) (x :== a) p :=
begin
  intros p x a s t H1 H2, cases H2, assumption
end

lemma seq_intro : ∀ (p q r:Pred) (e₁ e₂:Stmt),
  Hoare p e₁ q → Hoare q e₂ r → Hoare p (e₁ ;; e₂) r :=
begin
  intros p q r e₁ e₂ H1 H2 s t H3 H4, unfold Hoare at H1, unfold Hoare at H2,
  cases H4 with _ _ _ _ _ _ _ u _ H4 H5, apply (H2 u t),
    { apply (H1 s u); assumption },
    { assumption }
end

lemma ite_intro : ∀ (p q:Pred) (b:BExp) (e₁ e₂:Stmt),
  Hoare (λ s, p s ∧  b s) e₁ q →
  Hoare (λ s, p s ∧ ¬b s) e₂ q →
  Hoare p (ite b e₁ e₂) q :=
begin
  intros p q b e₁ e₂ H1 H2 s t H3 H4, unfold Hoare at H1, unfold Hoare at H2,
  cases H4 with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H5 ,
    { apply (H1 s t),
      { split; assumption },
      { assumption }},
    { apply (H2 s t),
      { split; assumption },
      { assumption }}
end

lemma while_intro : ∀ (p:Pred) (b:BExp) (e₁:Stmt),
  Hoare (λ s, p s ∧ b s) e₁ p → Hoare p (while b e₁) (λ s, p s ∧ ¬ b s) :=
begin
  intros p b e₁ H1 s t H2 H3, unfold Hoare at H1, revert H2,
  generalize H2 : while b e₁ = e, rw H2 at H3, revert H2,
  induction H3
  with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    s u t G1 G2 G3 G4 G5; intros H2,
    { cases H2 },
    { cases H2 },
    { cases H2 },
    { cases H2 },
    { cases H2 },
    { cases H2, clear H2, intros G6, apply G5,
      { refl},
      { apply (H1 s u),
        { split; assumption },
        { assumption }}},
    { cases H2, intros, split; assumption }
end

lemma weaken_intro : ∀ (p p' q q':Pred) (e₁:Stmt),
  (∀ s, p' s → p s) →
  Hoare p e₁ q      →
  (∀ s, q s → q' s) →
  Hoare p' e₁ q' :=
begin
  intros p p' q q' e₁ H1 H2 H3 s t H4 H5, unfold Hoare at H2,
  apply H3, apply (H2 s t),
    { apply H1, assumption },
    { assumption }
end

lemma weaken_left : ∀ (p p' q:Pred) (e₁:Stmt),
  (∀ s, p' s → p s) → Hoare p e₁ q → Hoare p' e₁ q :=
begin
  intros p p' q e₁ H1 H2, apply (weaken_intro p p' q q),
    { assumption },
    { assumption },
    { intros s H3, assumption }
end

lemma weaken_right : ∀ (p q q':Pred) (e₁:Stmt),
  Hoare p e₁ q → (∀ s, q s → q' s) → Hoare p e₁ q' :=
begin
  intros p q q' e₁ H1 H2, apply (weaken_intro p p q q'),
    {intros s H3, assumption },
    { assumption },
    { assumption }
end


lemma skip_intro' : ∀ (p q:Pred),
  (∀ s, p s → q s) → Hoare p skip q :=
begin
  intros p q H1, apply (weaken_left q p q),
    { assumption },
    { apply skip_intro }
end

lemma assign_intro' : ∀ (p q:Pred) (x:string) (a:AExp),
  (∀ s, p s → subst x a q s) → Hoare p (x :== a) q :=
begin
  intros p q x a H1, apply (weaken_left (subst x a q) p q),
    { assumption },
    { apply assign_intro }
end

lemma seq_intro' : ∀ (p q r:Pred) (e₁ e₂:Stmt),
  Hoare q e₂ r → Hoare p e₁ q → Hoare p (e₁ ;; e₂) r :=
begin
  intros p q r e₁ e₂ H1 H2, apply (seq_intro p q r); assumption
end

lemma while_intro' : ∀ (p q i:Pred) (b:BExp) (e₁:Stmt),
  Hoare (λ s, i s ∧ b s) e₁ i →
  (∀ s, p s → i s) →
  (∀ s, ¬b s → i s → q s) →
  Hoare p (while b e₁) q :=
begin
  intros p q i b e₁ H1 H2 H3,
  apply (weaken_intro i _ (λ s, i s ∧ ¬b s)),
    { assumption },
    { apply while_intro, assumption },
    { intros s H4, cases H4 with H4 H5, apply H3; assumption }
end
