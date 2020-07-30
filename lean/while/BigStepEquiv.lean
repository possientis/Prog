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
  intros e s t H1, induction H1 with _ x a s e₁ e₂ s u t H1 H2 IH1 IH2,
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
    {},
    {},
    {},
    {},
end
