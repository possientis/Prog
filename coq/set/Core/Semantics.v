Require Import Core.LEM.
Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Fresh.
Require Import Core.Syntax.
Require Import Core.ElemIncl.
Require Import Core.Environment.

Fixpoint eval (e:Env) (p:Formula) : Prop :=
    match p with
    | Bot           => False
    | Elem n m      => (e n) :: (e m)
    | Imp p1 p2     => eval e p1 -> eval e p2
    | All n p1      => forall (x:set), eval (bind e n x) p1
    end.

Lemma evalBot : forall (e:Env), eval e Bot <-> False.
Proof. intros e. unfold eval. split; intros H; assumption. Qed.

Lemma evalElem : forall (e:Env) (n m:nat), 
    eval e (Elem n m) <-> (e n) :: (e m).
Proof. intros e n m. unfold eval. split; intros H; assumption. Qed.

Lemma evalImp : forall (e:Env) (p q:Formula),
    eval e (Imp p q) <-> (eval e p -> eval e q).
Proof.
    intros e p q. unfold eval. fold (eval e p). fold (eval e q).
    split; intros H; assumption.
Qed.

Lemma evalAll : forall (e:Env) (p:Formula) (n:nat),
    eval e (All n p) <-> forall (x:set), eval (bind e n x) p.
Proof.
    intros e p n. unfold eval. split; intros H; assumption.
Qed.

Lemma evalNot : forall (e:Env) (p:Formula), 
    eval e (Not p) <-> ~ eval e p.
Proof. 
    intros e p. unfold Not, eval. fold (eval e p).
    split; intros H; assumption.
Qed.

Lemma evalOr : LEM -> forall (e:Env) (p q:Formula), 
    eval e (Or p q) <-> eval e p \/ eval e q.
Proof.
    intros L e p q. unfold Or, eval. simpl. 
    apply LEMOr. assumption.
Qed.

Lemma evalAnd : LEM -> forall (e:Env) (p q:Formula),
    eval e (And p q) <-> eval e p /\ eval e q.
Proof.
    intros L e p q. unfold And, eval. simpl. 
    apply LEMAnd. assumption.
Qed.

Lemma evalExi : LEM -> forall (e:Env) (p:Formula) (n:nat),
    eval e (Exi n p) <-> exists (x:set), eval (bind e n x) p.
Proof.
    intros L e p n. unfold Exi, eval, bind. simpl. 
    apply LEMExist. assumption.
Qed.

Lemma evalIff : LEM -> forall (e:Env) (p q:Formula),
    eval e (Iff p q) <-> (eval e p <-> eval e q).
Proof.
    intros L e p q. unfold Iff. apply evalAnd. assumption.
Qed.

Lemma evalSub : LEM -> forall (e:Env) (n m:nat), 
    eval e (Sub n m) <-> (e n) <== (e m).
Proof.
    intros L e n m. unfold Sub. rewrite elemIncl. 
    rewrite evalAll. simpl. split; intros H z.
    - remember (H z) as H' eqn:E. clear E.
      rewrite bindSame in H'.
      rewrite bindDiff in H'.
      rewrite bindDiff in H'.
        + assumption.
        + apply freshNot_m. 
        + apply freshNot_n.
    - rewrite bindSame.
      rewrite bindDiff.
      rewrite bindDiff.
        + apply H.
        + apply freshNot_m.
        + apply freshNot_n.
Qed.

Lemma evalEqu : LEM -> forall (e:Env) (n m:nat),
    eval e (Equ n m) <-> (e n) == (e m).
Proof.
    intros L e n m. unfold Equ, equal. 
    rewrite evalAnd, evalAll, evalAll. split; intros [H1 H2].
    - split; intros z.
        + remember (H1 z) as H1' eqn:E. clear E. 
          rewrite evalIff in H1'.
          rewrite evalElem in H1'.
          rewrite evalElem in H1'.
          rewrite bindSame in H1'.
          rewrite bindDiff in H1'.
          rewrite bindDiff in H1'.
            { assumption. }
            { apply freshNot_m. }
            { apply freshNot_n. }
            { assumption. }
        + remember (H2 z) as H2' eqn:E. clear E. 
          rewrite evalIff in H2'.
          rewrite evalElem in H2'.
          rewrite evalElem in H2'.
          rewrite bindSame in H2'.
          rewrite bindDiff in H2'.
          rewrite bindDiff in H2'.
            { assumption. }
            { apply freshNot_m. }
            { apply freshNot_n. }
            { assumption. }
    - split; intros z; 
      rewrite evalIff, evalElem, evalElem, bindSame, bindDiff, bindDiff.
        + apply H1.
        + apply freshNot_m.
        + apply freshNot_n.
        + assumption.
        + apply H2.
        + apply freshNot_m.
        + apply freshNot_n.
        + assumption.
    - assumption.
Qed.

(* Lemma 'inclRefl' expressed in set theory abstract syntax.                    *)
Definition inclReflF : Formula := All 0 (Sub 0 0).

(* The intent is to provide some validation to our semantics by going through   *)
(* several key set theoretic results and proving the equivalence between the    *)
(* evaluated abstract syntax and the corresponding Coq statement. However, the  *)
(* value of such exercise is limited as a Coq equivalence 'A <-> B' can always  *)
(* be proved whenever A and B are themselves provable. So 'A <-> B' does not in *)
(* itself prove that the propositions A and B are the 'same'. For our defense,  *)
(* we are proving the equivalence 'A <-> B' without using any result which      *)
(* asserts A or B. In particular, we make no use of the lemma 'inclRefl'.       *)
(* With this caveat in mind, we assert that evaluating inclReflF in any         *)
(* environment yields a proposition which is equivalent to the lemma inclRefl.  *)
Lemma evalInclReflF : LEM -> forall (e:Env),
    eval e inclReflF <-> forall (x:set), x <== x.
Proof.
    intros L e. unfold inclReflF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E. 
      rewrite evalSub in H'. 
        + rewrite bindSame in H'. assumption.
        + assumption.
    - rewrite evalSub.
        + rewrite bindSame. apply H.
        + assumption.
Qed.        


(* Theorem 'inclTrans' expressed in set theory abstract syntax.                 *)
Definition inclTransF : Formula := 
    All 0 (All 1 (All 2 (Imp (Sub 0 1) (Imp (Sub 1 2) (Sub 0 2))))).

(* Evaluating inclTransF in any environment 'yields' the theorem inclTrans.     *)
Lemma evalTransReflF : LEM -> forall (e:Env),
    eval e inclTransF <-> forall (x y z:set), x <== y -> y <== z -> x <== z. 
Proof.
    intros L e. unfold inclTransF. rewrite evalAll. split.
    - intros H x y z. 
      remember (H x) as H' eqn:E. clear E. clear H.
      rewrite evalAll in H'.
      remember (H' y) as H eqn:E. clear E. clear H'.
      rewrite evalAll in H.
      remember (H z) as H' eqn:E. clear E. clear H.
      rewrite evalImp in H'. rewrite evalImp in H'.
      rewrite evalSub in H'. rewrite evalSub in H'. rewrite evalSub in H'.
      remember (bind e 0 x) as e1 eqn:E1.
      remember (bind e1 1 y) as e2 eqn:E2.
      rewrite (bindDiff e2 2 0 z) in H'.
      rewrite (bindDiff e2 2 1 z) in H'.
      rewrite (bindSame e2 2 z) in H'.
      rewrite E2 in H'.
      rewrite (bindDiff e1 1 0 y) in H'.
      rewrite (bindSame e1 1 y) in H'.
      rewrite E1 in H'.
      rewrite (bindSame e 0 x) in H'.
      + assumption.
      + intros E. inversion E.
      + intros E. inversion E.
      + intros E. inversion E.
      + assumption.
      + assumption.
      + assumption.
    - intros H x. rewrite evalAll. intros y. rewrite evalAll. intros z.
      remember (bind e 0 x) as e1 eqn:E1.
      remember (bind e1 1 y) as e2 eqn:E2.
      remember (bind e2 2 z) as e3 eqn:E3.
      rewrite evalImp, evalImp, evalSub, evalSub, evalSub, E3. 
      rewrite (bindDiff e2 2 0 z).
      rewrite (bindDiff e2 2 1 z).
      rewrite (bindSame e2 2 z).
      rewrite E2.
      rewrite (bindDiff e1 1 0 y).
      rewrite (bindSame e1 1 y).
      rewrite E1.
      rewrite (bindSame e 0 x).
      + apply H.
      + intros E. inversion E.
      + intros E. inversion E.
      + intros E. inversion E.
      + assumption.
      + assumption.
      + assumption.
Qed.

(* Theorem 'elemIncl' expressed in set theory abstract syntax.                  *)
Definition elemInclF : Formula :=
    All 0 (All 1 (Iff (Sub 0 1) (All 2 (Imp (Elem 2 0) (Elem 2 1))))).

(* Evaluating elemInclF in any environment 'yields' the theorem elemIncl.       *)
Lemma evalElemInclF : LEM -> forall (e:Env), eval e elemInclF <-> 
    forall (x y:set), (x <== y <-> forall (z:set), z :: x -> z :: y). 
Proof.
    intros L e. unfold elemInclF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E. clear H.
      rewrite evalAll in H'. intros y.
      remember (H' y) as H eqn:E. clear E. clear H'.
      rewrite evalIff in H. rewrite evalSub in H.
      rewrite evalAll in H. 
      remember (bind e 0 x)  as e1 eqn:E1.
      remember (bind e1 1 y) as e2 eqn:E2.
      destruct H as [H1 H2]. split; intro H0.
        + intros z. rewrite E2 in H1.
          rewrite bindDiff in H1. rewrite bindSame in H1.
          rewrite E1 in H1. rewrite bindSame in H1.
          remember (H1 H0) as H1' eqn:E. clear E. clear H1.
          remember (H1' z) as H1  eqn:E. clear E. clear H1'.
          rewrite evalImp in H1. rewrite evalElem in H1. rewrite evalElem in H1.
          rewrite <- E1 in H1. rewrite <- E2 in H1.
          rewrite bindSame in H1. rewrite bindDiff in H1. rewrite bindDiff in H1.
          rewrite E2 in H1. rewrite bindSame in H1. rewrite bindDiff in H1.
          rewrite E1 in H1. rewrite bindSame in H1.
            { assumption. }
            { intros E. inversion E. }
            { intros E. inversion E. }
            { intros E. inversion E. }
            { intros E. inversion E. }
        + rewrite E2 in H2. rewrite bindSame in H2. rewrite bindDiff in H2.
          rewrite E1 in H2. rewrite bindSame in H2. apply H2.
          intros z. rewrite evalImp, evalElem, evalElem, <- E1, <- E2.
          rewrite bindSame, bindDiff, bindDiff, E2, bindDiff, bindSame. 
          rewrite E1, bindSame. apply H0.
            { intros E. inversion E. }
            { intros E. inversion E. }
            { intros E. inversion E. }
            { intros E. inversion E. }
        + assumption.
        + assumption. 
    - rewrite evalAll. intros y. rewrite evalIff, evalSub, evalAll.
      remember (bind e 0 x)  as e1 eqn:E1.
      remember (bind e1 1 y) as e2 eqn:E2.
      split; intros H0.
        + intros z. rewrite evalImp, evalElem, evalElem.
          rewrite bindSame, bindDiff, bindDiff. apply H.
            { assumption. }
            { intros E. inversion E. }
            { intros E. inversion E. }
        + apply H. intros z.
          remember (H0 z) as H' eqn:E. clear E. clear H0.
          rewrite evalImp in H'. rewrite evalElem in H'. rewrite evalElem in H'.
          rewrite bindSame in H'. rewrite bindDiff in H'. rewrite bindDiff in H'.
            { assumption. }
            { intros E. inversion E. }
            { intros E. inversion E. }
        + assumption.
        + assumption.
Qed.

(* Lemma 'equalRefl' expressed in set theory abstract syntax.                   *)
Definition equalReflF : Formula := All 0 (Equ 0 0).

(* Evaluating equalReflF in any environment 'yields' the lemma equalRefl.       *)
Lemma evalEqualReflF : LEM -> forall (e:Env), 
    eval e equalReflF <-> forall (x:set), x == x.
Proof.
    intros L e. unfold equalReflF. rewrite evalAll. split; intros H x.
    - remember (H x) as H' eqn:E. clear E. clear H.
      rewrite evalEqu in H'. rewrite bindSame in H'. 
        + assumption.
        + assumption.
    - rewrite evalEqu, bindSame. apply H.
        + assumption.
Qed.

(* Lemma 'equalSym' expressed in set theory abstract syntax.                    *)
Definition equalSymF : Formula := All 0 (All 1 (Imp (Equ 0 1) (Equ 1 0))).

(* Evaluating equalSymF in any environment 'yields' the lemma equalSym.         *)
Lemma evalEqualSymF : LEM -> forall (e:Env), 
    eval e equalSymF <-> forall (x y:set), x == y -> y == x.
Proof.
    intros L e. unfold equalSymF. rewrite evalAll. split; intros H x.
    - intros y.
      remember (H  x) as H' eqn:E. clear E. clear H. rewrite evalAll in H'. 
      remember (H' y) as H  eqn:E. clear E. clear H'.
      rewrite evalImp in H. rewrite evalEqu in H. rewrite evalEqu in H.
      remember (bind e 0 x) as e1 eqn:E1.
      rewrite bindSame in H. rewrite bindDiff in H. rewrite E1 in H.
      rewrite bindSame in H.
        + assumption.
        + intros E. inversion E.
        + assumption.
        + assumption.
    - rewrite evalAll. intros y. remember (bind e 0 x) as e1 eqn:E1.
      rewrite evalImp, evalEqu, evalEqu, bindSame, bindDiff, E1, bindSame.
        + apply H.
        + intros E. inversion E.
        + assumption.
        + assumption.
Qed.

(* Lemma 'equalTrans' expressed in set theory abstract syntax.                  *)
Definition equalTransF : Formula := 
    All 0 (All 1 (All 2 (Imp (Equ 0 1) (Imp (Equ 1 2) (Equ 0 2))))).

(*
(* Evaluating equalTransF in any environment 'yields' the lemma equalTrans.     *)
Lemma evalEqualTransF : LEM -> forall (e:Env), 
    eval e equalTransF <-> forall (x y z:set), x == y -> y == z -> x == z.
Proof.
    intros L e. unfold equalTransF. rewrite evalAll. split; intros H x.
    - intros y z.
      remember (H x) as H' eqn:E. clear E. clear H. rewrite evalAll in H'.
      remember (H' y) as H eqn:E. clear E. clear H'. rewrite evalAll in H.
      remember (H z) as H' eqn:E. clear E. clear H.

Show.
*)

(*
(* Theorem 'emptySet' expressed in set theory abstract syntax.                  *)
Definition emptySetF : Formula := Exi 0 (All 1 (Not (Elem 1 0))).

Lemma evalEmptySetF : LEM -> forall (e:Env),
    eval e emptySetF <-> exists (x:set), forall (z:set), ~ (z :: x).
Proof.
    intros L e. apply evalExi. assumption.
Qed.
*)
