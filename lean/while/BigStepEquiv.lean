import Stmt
import BigStep
import CloReduce

open Stmt

lemma BigStepCloReduce : forall (e:Stmt) (s t:Env),
  BigStep e s t → CloReduce e s skip t :=
begin
  intros e s t H1, induction H1 with _ x a s e₁ e₂ s u t H1 H2 IH1 IH2,
    { constructor },
    { constructor, constructor, constructor },
    { },
    {},
    {},
    {},
    {},
end
