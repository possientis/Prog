Require Import Func.

Definition Computable (a b:Type) (f:a ==> b) : Prop :=
    exists f':a -> b, f = toFunc f'.

Arguments Computable {a} {b} _.

Lemma idFunc_Computable : forall (a:Type), Computable (idFunc a).
Proof.
    intros a. unfold Computable. exists id. symmetry. apply toFunc_id.
Qed.

Lemma compose_Computable : forall (a b c:Type) (f:a ==> b) (g:b ==> c),
    Computable f -> Computable g -> Computable (f ; g).
Proof.
    intros a b c f g [f' Hf] [g' Hg]. exists (g' @ f'). symmetry.
    rewrite Hf, Hg. apply toFunc_compose.
Qed.




