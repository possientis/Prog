import HoareSyntax
import BigStep

open Hoare

lemma HoareSound : ∀ (p q:Pred) (e:Stmt) (s t:Env),
  Hoare p e q → p s → BigStep e s t → q t :=
begin
  intros p q e s t H1, revert s t,
  induction H1 with p p x a; intros s t H1 H2,
    { cases H2, assumption },
    { unfold subst at H1, cases H2, assumption },
    {},
    {},
    {},
    {}
end
