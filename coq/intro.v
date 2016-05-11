Lemma structured_intro_example1: forall A B C:Prop, A/\B/\C -> A.
Proof.
  intros A B C [Ha [Hb Hc]].

(*

 A : Prop
 B : Prop
 C : Prop
 Ha : A
 Hb : B
 Hc : C
 ============================
  A
*)

Abort.

Lemma structured_intro_example2: forall A B:Prop, A\/B/\(B->A)->A.
Proof.
 intros A B [Ha | [Hb Hi]]. 
