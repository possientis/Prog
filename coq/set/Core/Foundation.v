(* NEXT: ===> ???                                                               *)


Require Import Le.

Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Rank.
Require Import Core.Order.
Require Import Core.Equal.
Require Import Core.Trans.
Require Import Core.Empty.
Require Import Core.ElemIncl.
Require Import Core.Decidability. 
Require Import Core.Extensionality.

(* In this module, we prove that the foundation axiom is satisfied in our       *)
(* model. Of course, the foundation axiom like other axioms of ZF, has more     *)
(* than one possible formulation. These various formulations are known to be    *)
(* equivalent within ZF, but it is far from obvious that they should still be   *)
(* so within our model. This caveat may apply to other axioms which we have     *)
(* previously proven (pairing, union, powerset). So we shall prove one possible *)
(* formulation of the foundation axiom which states that every non-empty set    *)
(* has an element which is minimal for the membership relation. A set x is said *)
(* to be minimal (for ::) in xs, if and only if x is an element of xs, and no   *)
(* element of xs belongs to x.                                                  *)
Definition minimal (x xs:set) : Prop :=
    x :: xs /\ ~ exists (y:set), y :: xs /\ y :: x.

(* No set has an element which is larger or equal to itself. This result is not *)
(* needed for proving the foundation axiom, but will allow us to show that no   *)
(* set belongs to itself, which is interesting in its own right. These results  *)
(* are obtained without making use of the notion of 'rank' seen previously.     *)
(* So if x is a subset of y, y cannot belong to x.                              *)
Lemma coherence : forall (x y:set), x <== y -> ~ y :: x.
Proof.
    induction x as [|x IH1 xs IH2].
    - intros y _. apply emptyCharac.
    - intros y H1 H2. apply consElem in H2. destruct H2 as [H2|H2].
        + apply (IH1 x).
            { apply inclRefl. }
            { apply equal_r with y.
                { assumption. }
                { apply elemIncl with (Cons x xs).
                    { assumption. }
                    { apply consElem. left. apply equal_refl. }}}
        + apply (IH2 y).
            { apply inclTrans with (Cons x xs).
                { apply elemIncl. intros z H. apply consElem. right. assumption. }
                { assumption. }}
            { assumption. }
Qed.

(* No set contains itself                                                       *)
Lemma noSelfElem : forall (x:set), ~ x :: x.
Proof.
    intros x. apply coherence. apply inclRefl.
Qed.

(* Incidentally, if no set can contain itself, there can be no 'universe', i.e. *)
(* there exists no set which contains every other set. So the universe of sets  *)
(* does exist but only at the Coq meta-theoretic level, i.e. as the type 'set'. *)
Lemma noUniverse : ~ exists (x:set), forall (y:set), y :: x.
Proof.
    intros [x H]. apply (noSelfElem x). apply H.
Qed.


(* The foundation axiom is true: every non-empty set has a ::-minimal element.  *)
(* We crucially need to make use of the notion of 'rank' of the Rank module.    *)
Theorem foundation : forall (x:set), ~(x == Nil) -> 
    exists (y:set), minimal y x.
Proof.
    intros x H. rewrite emptyIsNil in H. 
    destruct (rankMinimal x H) as [y [H1 H2]]. exists y. split.
    - assumption.
    - intros H3. destruct H3 as [z [H3 H4]].
      assert (S (rank z) <= rank z) as H5.
        { apply le_trans with (rank y).
            { apply rankElem. assumption. }
            { apply H2. assumption. }}
      apply (not_le_s_n (rank z)). assumption.
Qed.

(* The following statement is not a set theoretic statement as it involves      *)
(* the Coq notion of function of type nat -> set. However, it is interesting to *)
(* see that the notion of 'rank' allows us to prove that there can be no 'Coq'  *)
(* sequence of sets which form an infinite descent via the membership relation. *)
Lemma noDescendingSeq : ~ exists (f:nat -> set), forall (n:nat), f (S n) :: f n.
Proof.
    intros [f H]. apply noDecreasingSeq. 
    exists (fun n => rank (f n)). 
    intros n. apply rankElem. apply H.
Qed.
