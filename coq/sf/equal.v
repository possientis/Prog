Require Import induction.

Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.


Axiom functional_extensionality : forall (a b:Type) (f g:a -> b),
    (forall x, f x = g x) -> f = g.

 
Lemma plus_comm_ext : plus = fun n m => m + n.
Proof.
    apply functional_extensionality. intros x.
    apply functional_extensionality. intros y.
    apply plus_comm.
Qed.

(*
Print Assumptions plus_comm_ext.
*)





