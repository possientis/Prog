Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Nat.Eq.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Syntax.

(* Custom notations for predicates of 3 arguments appear to fail in Coq.        *)
(* Creating intermediary types Binding and Interpretation to bypass the issue.  *)
Inductive Binding : Type :=
| mkBind : forall (n:nat) (x:set), Binding
.

Notation "n ~> x" := (mkBind n x)
    (at level 1, no associativity) : Context_scope.

Inductive Context : Type :=
| O        : Context
| CtxSnoc  : Context -> Binding -> Context
.

Notation "G ';' x" := (CtxSnoc G x)
    (at level 50, left associativity) : Context_scope.

Open Scope Context_scope.

Inductive Find : Context -> Binding -> Prop :=
| FindZ : forall (G:Context) (n:nat) (x:set), Find (G ; n~>x) n~>x
| FindS : forall (G:Context) (n m:nat) (x y:set),
    n <> m      -> 
    Find G n~>x -> 
    Find (G ; m~>y) n~>x
| FindE : forall (G:Context) (n:nat) (x y:set),
    x == y      ->
    Find G n~>x ->
    Find G n~>y
.

Notation "G ':>' x" := (Find G x)
    (at level 60, no associativity) : Context_scope.

Open Scope Context_scope.

(* Just restating constructor FindZ with custom notations.                      *)
Lemma findZ : forall (G:Context) (n:nat) (x:set), G ; n~>x :> n~>x. 
Proof.
    intros G n x. constructor.
Qed.

(* Just restating constructor FindS with custom notations.                      *)
Lemma findS : forall (G:Context) (n m:nat) (x y:set),
    n <> m -> G :> n~>x -> G ; m~>y :> n~>x.
Proof.
    intros G n m x y H1 H2. constructor; assumption.
Qed.

(* Just restating constructor FindS with custom notations.                      *)
Lemma findE : forall (G:Context) (n:nat) (x y:set),
    x == y -> G :> n~>x -> G :> n~>y.
Proof.
    intros G n x y H1 H2. apply FindE with x; assumption.
Qed.

Definition ctxIncl (G H:Context) : Prop :=
    forall (n:nat) (x:set), G :> n~>x -> H :> n~>x.

Notation "G <= H"  := (ctxIncl G H)
    (at level 70, no associativity) : Context_scope.

Open Scope Context_scope.

(* The corresponding proof in agda appears to be a lot simpler.                 *)
Lemma ctxInclExtend : forall (G H:Context) (n:nat) (x:set),
    G <= H -> G ; n~>x <= H ; n~>x.
Proof.
    intros G H n x. unfold ctxIncl. intros H2 m y H3.
    remember (G ; n~>x) as G' eqn:G1. remember (H ; n~>x) as H' eqn:H1. 
    remember (m~>y) as b eqn:H4.
    revert m y H H' G n x H4 H2 G1 H1.
    induction H3 as [G' n' x'|G' n' m' x' y' Hnm H1 IH|G' n' x' y' Hxy H1 IH];
    intros n x H H' G m y H2 H3 H4 H5; inversion H2; subst; clear H2.
    - inversion H4. subst. clear H4. apply findZ.
    - inversion H4. subst. clear H4. apply findS; 
      try assumption. apply H3. assumption.
    - apply findE with x'; try assumption.
      apply (IH n x' H (H ; m~>y) G m y); try reflexivity. assumption.
Qed.

Lemma ctxInclRefl : forall (G:Context), G <= G.
Proof.
    unfold ctxIncl. intros G n x. auto.
Qed.

Lemma ctxInclTrans : forall (G H K:Context), G <= H -> H <= K -> G <= K.
Proof.
    unfold ctxIncl. intros G H K H1 H2 n x H3. apply H2, H1. assumption.
Qed.

Definition ctxEqual (G G':Context) : Prop := G <= G' /\ G' <= G.

Lemma ctxEqualRefl : forall (G:Context), ctxEqual G G.
Proof.
    intros G. split; apply ctxInclRefl.
Qed.

Lemma ctxEqualSym : forall (G G':Context), ctxEqual G G' -> ctxEqual G' G.
Proof.
    intros G G' [H1 H2]. split; assumption.
Qed.

Lemma ctxEqualTrans : forall (G1 G2 G3:Context), 
    ctxEqual G1 G2 -> ctxEqual G2 G3 -> ctxEqual G1 G3.
Proof.
    intros G1 G2 G3 [H1 H2] [H3 H4]. split; 
    apply ctxInclTrans with G2; assumption.
Qed.

Definition ctxEqualOn (p:Formula) (G G':Context) : Prop :=
    forall (n:nat) (x:set), In n (Fr p) -> G :> n~>x <-> G' :> n~>x.

Lemma ctxEqualOnRefl : forall (p:Formula) (G:Context), ctxEqualOn p G G.
Proof.
    intros p G n x H1. split; auto.
Qed.

Lemma ctxEqualOnSym : forall (p:Formula) (G G':Context),
    ctxEqualOn p G G' -> ctxEqualOn p G' G.
Proof.
    intros p G G' H1 n x H2. destruct (H1 n x H2) as [H3 H4]. split; assumption.
Qed.

Lemma ctxEqualOnTrans : forall (p:Formula) (G1 G2 G3: Context),
    ctxEqualOn p G1 G2 -> ctxEqualOn p G2 G3 -> ctxEqualOn p G1 G3.
Proof.
    intros p G1 G2 G3 H1 H2 n x H3. 
    destruct (H1 n x H3) as [H4 H5].
    destruct (H2 n x H3) as [H6 H7]. split; intros H8.
    - apply H6, H4. assumption.
    - apply H5, H7. assumption.
Qed.

Lemma ctxEqualctxEqualOn : forall (p:Formula) (G G':Context),
    ctxEqual G G' -> ctxEqualOn p G G'.
Proof.
    intros p G G' [H1 H2] n x H3. split.
    - apply H1.
    - apply H2.
Qed.

(* Not very useful. Just following the parallel with Environment.               *)
Definition bind (G:Context) (n:nat) (x:set) : Context := G ; n~>x. 

Lemma bindSame : forall (G:Context) (n:nat) (x:set), bind G n x :> n~>x.
Proof.
    intros G n x. apply findZ.
Qed.

Lemma bindDiff : forall (G:Context) (n m:nat) (x y:set), n <> m -> 
    bind G n x :> m~>y <-> G :> m~>y.
Proof.
    intros G n m x y H1. split; intros H2.
    - unfold bind in H2. 
      remember (G ; n~>x) as G' eqn:E. revert G E.
      remember (m~>y) as b eqn:E. revert n m x y H1 E.
      induction H2 as [G' n' x'|G' n' m' x' y' H1 H2 IH|G' n' x' y' H1 H2 IH];
      intros n m x y H3 H4 G H5.
        + exfalso. inversion H5. subst. clear H5. 
          inversion H4. subst. apply H3. reflexivity.
        + inversion H5. subst. assumption.
        + inversion H4. subst. clear H4. apply findE with x'; try assumption.
          apply (IH n m x x'); try reflexivity. assumption.
    - apply FindS; try assumption. intros H3. subst. apply H1. reflexivity.
Qed.

Lemma bindEqual : forall (G:Context) (n m:nat) (x y z:set),
    x == y -> bind G n x :> m~>z <-> bind G n y :> m~>z.
Proof.
    intros G n m x y z H1. split; intros H2.
    - unfold bind in H2.
      remember (G ; n~>x) as G' eqn:E. revert G E.
      remember (m~>z) as b eqn:E. revert n m x y z H1 E.
      induction H2 as [G' n' x'|G' n' m' x' y' H1 H2 IH|G' n' x' y' H1 H2 IH];
      intros n m x y z H3 H4 G H5.
        + inversion H5. subst. clear H5. inversion H4. subst. clear H4.
          unfold bind. apply findE with y.
            { apply equalSym. assumption. }
            { apply FindZ. }
        + inversion H5. subst. clear H5. inversion H4. subst. clear H4.
          unfold bind. apply findS; assumption.
        + inversion H4. subst. clear H4. apply findE with x'; try assumption.
          apply (IH n m x y x'); try assumption; try reflexivity.
    - unfold bind in H2.
      remember (G ; n~>y) as G' eqn:E. revert G E.
      remember (m~>z) as b eqn:E. revert n m x y z H1 E.
      induction H2 as [G' n' x'|G' n' m' x' y' H1 H2 IH|G' n' x' y' H1 H2 IH];
      intros n m x y z H3 H4 G H5.
        + inversion H5. subst. clear H5. inversion H4. subst. clear H4.
          unfold bind. apply findE with x.
            { assumption. }
            { apply FindZ. }
        + inversion H5. subst. clear H5. inversion H4. subst. clear H4.
          unfold bind. apply findS; assumption.
        + inversion H4. subst. clear H4. apply findE with x'; try assumption.
          apply (IH n m x y x'); try assumption; try reflexivity.
Qed.

Lemma bindEqual' : forall (G:Context) (n:nat) (x y:set),
    x == y -> ctxEqual (bind G n x) (bind G n y).
Proof.
    intros G n x y H1. split; intros m z H2. 
    - rewrite (bindEqual G n m y x z); try assumption.
      apply equalSym. assumption.
    - rewrite (bindEqual G n m x y z); try assumption.
Qed.

Lemma bindEqualRev : forall (G:Context) (n:nat) (x y:set),
    G ; n~>x :> n~>y -> x == y.
Proof.
    intros G n x y H1. remember (G ; n~>x) as G' eqn:H2.
    remember (n~>y) as b eqn:H3. revert G n x y H2 H3.
    induction H1 as [G' n' x'|G' n' m' x' y' H1 H2 IH|G' n' x' y' H1 H2 IH ]; 
    intros G n x y H3 H4. 
    - inversion H3. subst. clear H3. inversion H4. apply equalRefl.
    - inversion H3. subst. clear H3. inversion H4. subst. clear H4.
      exfalso. apply H1. reflexivity.
    - inversion H4. subst. clear H4. apply equalTrans with x';
      try assumption. apply (IH G n x x'); reflexivity.
Qed.


Lemma bindPermute : forall (G:Context) (n m:nat) (x y:set), m <> n ->
    ctxEqual (bind (bind G n x) m y) (bind (bind G m y) n x).
Proof.
    intros G n m x y Hmn. unfold bind. split; intros p z H1;
    destruct (eqDec m p) as [H2|H2]; destruct (eqDec n p) as [H3|H3].
    - subst. exfalso. apply Hmn. reflexivity.
    - subst. apply bindDiff; try assumption. apply FindE with y.
        + apply bindEqualRev in H1. assumption.
        + constructor.
    - subst. apply bindDiff in H1; try assumption. apply FindE with x.
        + apply bindEqualRev in H1. assumption.
        + constructor.        
    - apply bindDiff; try assumption. apply bindDiff; try assumption.
      apply bindDiff in H1; try assumption. apply bindDiff in H1; assumption.
    - subst. exfalso. apply Hmn. reflexivity.
    - subst. apply bindDiff in H1; try assumption. apply bindEqualRev in H1.
      apply FindE with y; try assumption. constructor.
    - subst. apply bindDiff; try assumption. apply FindE with x;
      try (apply FindZ). apply bindEqualRev in H1. assumption.
    - apply bindDiff; try assumption. apply bindDiff; try assumption.
      apply bindDiff in H1; try assumption. apply bindDiff in H1; assumption.
Qed.

Lemma bindOver : forall (G:Context) (n:nat) (x y:set),
    ctxEqual (bind (bind G n x) n y) (bind G n y).
Proof.
    intros G n x y. unfold bind. split; intros m z H1;
    destruct (eqDec n m) as [H2|H2].
    - subst. apply FindE with y; try (apply FindZ).
      apply bindEqualRev in H1. assumption.
    - apply bindDiff; try assumption.
      apply bindDiff in H1; try assumption. apply bindDiff in H1; assumption.
    - subst. apply FindE with y; try (apply FindZ).
      apply bindEqualRev in H1. assumption.
    - apply bindDiff; try assumption. apply bindDiff; try assumption.
      apply bindDiff in H1; assumption.
Qed.

Lemma bindCtxEqual : forall (G G':Context) (n:nat) (x x':set),
    ctxEqual G G' -> x == x' -> ctxEqual (bind G n x) (bind G' n x').
Proof.
    intros G G' n x x' [H1 H2] H3. unfold bind. split; intros m y H4;
    destruct (eqDec n m) as [H5|H5].
    - subst. apply FindE with x'; try (apply FindZ). apply equalTrans with x.
        + apply equalSym. assumption.
        + apply bindEqualRev in H4. assumption.
    - apply bindDiff; try assumption. apply bindDiff in H4; try assumption.
      apply H1. assumption.
    - subst. apply FindE with x; try (apply FindZ). 
      apply bindEqualRev in H4. apply equalTrans with x'; assumption.
    - apply bindDiff; try assumption. apply bindDiff in H4; try assumption.
      apply H2. assumption.
Qed.

(*
Lemma bindCtxEqualOn : forall (p:Formula) (G G':Context) (n:nat) (x x':set),
    ctxEqualOn p G G' -> x == x' -> ctxEqualOn p (bind G n x) (bind G' n x').
Proof.
    intros p G G' n x x' H1 H2 m y H3. split; intros H4;
    destruct (eqDec n m) as [H5|H5].
    - subst. apply FindE with x'; try (apply FindZ). apply equalTrans with x.
        + apply equalSym. assumption.
        + apply bindEqualRev in H4. assumption.
    -
Show.
*)
