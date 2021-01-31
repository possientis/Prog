Require Import Logic.Axiom.Dec.
Require Import Logic.Axiom.Sat.
Require Import Logic.Axiom.Witness.

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
    exists (fun f => f). intros f. split; auto.
Qed.

(* Difficult result which requires the use of the witness operator              *)
Definition toDec : forall (X:Prop), (X \/ ~X) -> Sec X -> Sec (~X) -> Dec X.
Proof.
    intros X H1 [f H2] [g H3]. 
    remember (fun n => orb (f n) (g n)) as h eqn:E.
    assert (tsat h) as H4.
        { rewrite E. apply tsatOr. destruct H1 as [H1|H1].
            - left.  destruct H2 as [H2 G2]. apply H2. assumption.
            - right. destruct H3 as [H3 G3]. apply H3. assumption. }
    remember (fun n => h n = true) as p eqn:P.
    assert (pDec p) as q.
        { intros n. rewrite P, E. destruct (f n), (g n).
            - left. reflexivity.
            - left. reflexivity.
            - left. reflexivity.
            - right. intros H5. inversion H5. }
    assert (sig p) as H5.
        { apply witness; try assumption. rewrite E in H4. 
          rewrite P, E. assumption. }
    destruct H5 as [n H5]. rewrite P in H5. rewrite E in H5.
    destruct (f n) eqn:H6; destruct (g n) eqn:H7.
    - left.  destruct H2 as [H2 G2]. apply G2. exists n. assumption.
    - left.  destruct H2 as [H2 G2]. apply G2. exists n. assumption.
    - right. destruct H3 as [H3 G3]. apply G3. exists n. assumption.
    - inversion H5.
Qed.

