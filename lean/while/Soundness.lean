import HoareSyntax
import BigStep

open Hoare

lemma HoareSound : ∀ (p q:Pred) (e:Stmt) (s t:Env),
  Hoare p e q → p s → BigStep e s t → q t :=
begin
  intros p q e s t H1, revert s t,
  induction H1
    with p p x a p q r e₁ e₂ H1 H2 H3 H4 p q b e₁ e₂ H1 H2 H3 H4 p b e₁ H3 H4
         p p' q q' e₁ H3 H4 H5 H6;
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
    { clear H3, revert H1, revert H4, generalize H5 : Stmt.while b e₁ = e,
      rw H5 at H2, revert e₁ H5, clear q,
      induction H2 with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      b e₂ s u t H1 H2 H3 H4 H5;
      intros e₁ H1,
        { cases H1 },
        { cases H1 },
        { cases H1 },
        { cases H1 },
        { cases H1 },
        { cases H1, intros H6 H7, apply (H5 e₂),
          { refl },
          { assumption },
          { apply (H6 s),
            { split; assumption },
            { assumption }}},
        { intros H3 H4, assumption }},
    { clear e, apply H5, apply H6,
      { apply H3, assumption },
      { assumption }}
end
