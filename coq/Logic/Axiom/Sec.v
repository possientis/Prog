Require Import Logic.Axiom.Dec.
Require Import Logic.Axiom.Sat.

(* A proposition has a semi-decider                                             *)
Definition Sec (A:Prop) : Type := sig (fun f => A <-> tsat f). 

(* The function F is a semi-decider of the predicate p.                         *)
Definition SemiDeciderOf (a:Type) (p:a -> Prop)(F:a -> nat -> bool) : Prop :=
    forall (x:a), p x <-> tsat (F x).

Arguments SemiDeciderOf {a}.

(* A predicate is semi-decidable iff it has a semi-decider.                     *)
Definition SemiDecidable (a:Type) (p:a -> Prop) : Prop :=
    exists (F:a -> nat -> bool), SemiDeciderOf p F.

Arguments SemiDecidable {a}.

Definition CoSemiDecidable (a:Type) (p:a -> Prop) : Prop :=
    SemiDecidable (fun x => ~p x).

Arguments CoSemiDecidable {a}.

Lemma tsatSemiDecidable : SemiDecidable tsat.
Proof.
    exists (fun f n => f n). intros f. split; auto.
Qed.

(*
Definition toDec : forall (X:Prop), (X \/ ~ X) -> Sec X -> Sec (~X) -> Dec X.
Proof.
    intros X H1 [f H2] [g H3].
Show.
*)
