(* tauto specifically for propositional logic *)
(* will succeed where auto will fail *)

Lemma example_for_tauto1 : forall A B:Prop, A/\B->A.
Proof.
  tauto.
Qed.

Lemma example_for_tauto2: forall A B:Prop, A/\~A->B.
Proof.
  tauto.
Qed.

Require Import ZArith.
Open Scope Z_scope.
Lemma example_for_tauto3: forall x y:Z, x<=y -> ~(x<=y) -> x = 3.
Proof.
  tauto.
Qed.

Lemma example_for_tauto4: forall A B:Prop, A\/B -> B\/A.
Proof.
  tauto.
Qed.

Lemma example_for_tauto5: forall A B C D:Prop, (A->B)\/(A->C)->A->(B->D)->(C->D)->D.
Proof.
  tauto.
Qed.


