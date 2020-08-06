import Stmt
import BigStep
import Reduce
import CloReduce

open Stmt
open Reduce
open CloReduce

lemma SeqCompatL : ∀ (e₁ e₁' e₂:Stmt) (s s':Env),
  CloReduce e₁ s e₁' s' → CloReduce (e₁ ;; e₂) s (e₁' ;; e₂) s' :=
begin
  intros e₁ e₁' e₂ s s' H1, induction H1 with _ _ e₁ e₁' e₁'' s₁ s₁' s₁'' H1 H2 H3,
    { constructor },
    { apply cloStep,
      { apply SEQ_STEP, assumption},
      { assumption}}
end

lemma BigStepCloReduce : ∀ (e:Stmt) (s t:Env),
  BigStep e s t → CloReduce e s skip t :=
begin
  intros e s t H1, induction H1 with
    _ x a s e₁ e₂ s u t H1 H2 IH1 IH2 b e₁ e₂ s t H1 H2 H3
    b e₁ e₂ s t H1 H2 H3 b e₁ s u t H1 H2 H3 H4 H5 b e₁ s H1,
    { constructor },
    { constructor, constructor, constructor },
    { cases IH1 with _ _ _ e₁' _ _ s' _ H1 H2,
      { constructor,
        { apply SEQ_SKIP },
        { assumption }},
      { apply CloReduceTrans,
        { apply SeqCompatL, apply cloStep,
          { apply H1},
          { apply H2}},
        { apply cloStep,
          { apply SEQ_SKIP },
          { assumption }}}},
    { apply cloStep,
      { constructor, assumption },
      { assumption }},
    { apply cloStep ,
      { apply IF_F, assumption },
      { assumption }},
    { apply CloReduceTrans _ (while b e₁) skip s u t,
      { apply CloReduceTrans _ (skip ;; while b e₁) _ s u u,
        { apply CloReduceTrans _ (e₁ ;; while b e₁) _ _ s _,
          { apply CloReduceTrans _ (ite b (e₁ ;; while b e₁) skip) _ _ s _,
            { apply cloStep; constructor},
            { apply cloStep _ (e₁ ;; while b e₁) _ _ s _,
              { constructor, assumption },
              { constructor }}},
          { apply SeqCompatL, assumption }},
        { apply cloStep _ (while b e₁) _ _ u _; constructor }},
      { assumption }},
    { apply cloStep _ (ite b (e₁ ;; while b e₁) skip) _ _ s _,
      { constructor },
      { apply cloStep _ skip _ _ s _,
        { apply IF_F, assumption },
        { constructor }}},
end

lemma ReduceBigStep : ∀ (e₁ e₂:Stmt) (s₁ s₂ s₃:Env),
  Reduce e₁ s₁ e₂ s₂ → BigStep e₂ s₂ s₃ → BigStep e₁ s₁ s₃ :=
begin
  intros e₁ e₂ s₁ s₂ s₃ H1, revert s₃,
  induction H1 with
    x a s e₁ e₁' e₂ s s' H1 H2 e₁ s₁ b e₁ e₂ s₁ H1 b e₁ e₂ s₁ H1 b e₁ s₁,
    { intros t H1, cases H1, constructor },
    { intros t H2, cases H2 with _ _ _ _ _ _ _ u _ H3 H4, constructor,
      { apply H2, apply H3 },
      { apply H4 }},
    { intros s₂ H1, constructor,
      { constructor },
      { assumption }},
    { intros s₂ H2, apply BigStep.IF_T; assumption },
    { intros s₂ H2, apply BigStep.IF_F; assumption },
    { intros s₂ H1, cases H1 with
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 _ _ _ _ _ H1 H2,
      { cases H2, { apply BigStep.WHILE_T; assumption }},
      { cases H2, apply BigStep.WHILE_F; assumption }}
end

lemma CloReduceBigStep : ∀ (e:Stmt) (s t:Env),
  CloReduce e s skip t → BigStep e s t :=
begin
  intros e₁ s₁ s₃ H1, generalize H2 : skip = e₃, rw H2 at H1, revert H2,
  induction H1 with e s e₁ e₂ e₃ s₁ s₂ s₃ H1 H2 H3,
    { intros H1, rw ← H1, constructor },
    { intros H4, apply ReduceBigStep,
      { assumption },
      { apply H3, assumption }}
end

lemma BigStepCloReduceEquiv : ∀ (e:Stmt) (s t:Env),
  BigStep e s t ↔ CloReduce e s skip t :=
begin
  intros e s t, split,
    { apply BigStepCloReduce },
    { apply CloReduceBigStep }
end

