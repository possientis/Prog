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

(* The set 'x' is ::-minimal in the set 'xs'                                    *)
Definition minimal (x xs:set) : Prop :=
    x :: xs /\ ~ exists (y:set), y :: xs /\ y :: x.

(* No set has an element which is larger or equal to itself                     *)
Lemma coherence : forall (x y:set), x <== y -> ~ y :: x.
Proof.
    induction x as [|x IH1 xs IH2].
    - intros y _. apply emptyCharac.
    - intros y H1 H2. apply consElem in H2. destruct H2 as [H2|H2].
        + apply (IH1 x).
            { apply incl_refl. }
            { apply equal_r with y.
                { assumption. }
                { apply elemIncl with (Cons x xs).
                    { assumption. }
                    { apply consElem. left. apply equal_refl. }}}
        + apply (IH2 y).
            { apply incl_trans with (Cons x xs).
                { apply elemIncl. intros z H. apply consElem. right. assumption. }
                { assumption. }}
            { assumption. }
Qed.

(* No set contains itself                                                       *)
Lemma noSelfElem : forall (x:set), ~ x :: x.
Proof.
    intros x. apply coherence. apply incl_refl.
Qed.


(* The foundation axiom is satisfied in 'set'                                   *) 
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

