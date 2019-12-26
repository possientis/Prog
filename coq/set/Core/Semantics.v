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

(*
(* Lemma 'inclTrans' expressed in set theory abstract syntax.                   *)
Definition inclTransF : Formula := 
    All 0 (All 1 (All 2 (Imp (Sub 0 1) (Imp (Sub 1 2) (Sub 0 2))))).

Lemma evalTransReflF : LEM -> forall (e:Env),
    eval e inclTransF <-> forall (x y z:set), x <== y -> y <== z -> x <== z. 
Proof.
    intros L e. unfold inclTransF. rewrite evalAll.

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
