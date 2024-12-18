Require Import ZF.Binary.Functional.
Require Import ZF.Class.
Require Import ZF.Class.Binary.
Require Import ZF.Set.OrdPair.

(* A class is said to be functional if its associated binary class is           *)
Definition Functional (P:Class) : Prop := Functional.Functional (toBinary P).

(* Characterisation of a functional class.                                      *)
Proposition FunctionalCharac : forall (P:Class), Functional P <->
  forall x y z, P :(x,y): -> P :(x,z): -> y = z.
Proof.
  intros P. split; intros H1.
  - apply H1.
  - unfold Functional, Binary.Functional.Functional, toBinary. assumption.
Qed.


