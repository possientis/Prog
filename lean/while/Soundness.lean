import HoareSyntax
import BigStep

open Hoare

lemma HoareSound : ∀ (p q:Pred) (e:Stmt) (s t:Env),
  Hoare p e q → p s → BigStep e s t → q t :=
begin
  intros p q e s t H1, revert s t,
  induction H1
    with p p x a p q r e₁ e₂ H1 H2 H3 H4 p q b e₁ e₂ H1 H2 H3 H4 p b e₁ H3 H4;
  intros s t H1 H2,
    { cases H2, assumption },
    { unfold subst at H1, cases H2, assumption },
    { cases H2 with _ _ _ _ _ _ _ u _ H5 H6, apply H4,
      { apply H3,
        { exact H1 },
        { exact H5 }},
      { assumption }},
    { cases H2 with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H6 _ _ _ _ _ H5 H6,
      { apply H3,
        { split; assumption },
        { assumption }},
      { apply H4,
        { split; assumption },
        { assumption }}},
    { cases H2
      with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u _ H5 H6 H7,
      {},
      {}},
    {}
end
