Import Nat.
Require Import List.
Require Import PeanoNat.

Require Import Logic.Axiom.LEM.
Require Import Logic.Rel.Prop.
Require Import Logic.Nat.Fresh.

Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.
Require Import Logic.Set.Empty.
Require Import Logic.Set.ElemIncl.
Require Import Logic.Set.Foundation.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Environment.

Fixpoint eval (e:Env) (p:Formula) : Prop :=
    match p with
    | Bot           => False
    | Elem n m      => (e n) :: (e m)
    | Imp p1 p2     => eval e p1 -> eval e p2
    | All n p1      => forall (x:set), eval (bind e n x) p1
    end.

Lemma evalCompat : forall (e e':Env) (p:Formula), 
    envEqual e e' -> eval e p <-> eval e' p.
Proof.
    intros e e' p. revert p e e'. 
    induction p as [ |n m|p1 IH1 p2 IH2|n p1 IH1]; intros e e' H1; simpl.
    - split; auto.
    - split; apply elemCompatLR; try (apply H1); 
      apply envEqualSym in H1; apply H1.
    - apply implyCompatLR.
        + apply IH1. assumption.
        + apply IH2. assumption.
    - apply allCompat. intros x. apply IH1, bindEnvEqual; try assumption.
      apply equalRefl.
Qed.

(* Given an environement e, a formula p and a variable n, we can define a       *)
(* predicate P: set -> Prop by defining P x as the proposition obtained by      *)
(* evaluating the formula p in an environment where n is bound to x.            *)
Definition eval1 (e:Env) (p:Formula) (n:nat) (x:set) : Prop :=
    eval (bind e n x) p.

(* Given an environement e, a formula p and two variables n m, we can define a  *)
(* two variables predicate P: set -> set -> Prop by defining P x y as the pro-  *)
(* position obtained by evaluating the formula p in an environment where n is   *)
(* bound to x and m is bound to y. This predicate makes sense if n <> m.        *)
Definition eval2 (e:Env) (p:Formula) (n m:nat) (x y:set) : Prop :=
    eval (bind (bind e n x) m y) p.

Definition eval3 (e:Env) (p:Formula) (n m k:nat) (x y z:set) : Prop :=
    eval (bind (bind (bind e n x) m y) k z) p.

Lemma eval3ToEval2 : forall (e:Env) (p:Formula) (n m k:nat) (x y z:set),
    eval3 e p n m k x y z <-> eval2 (bind e n x) p m k y z.
Proof.
    intros e p n m k x y z. unfold eval3, eval2. split; auto.
Qed.


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

(* LEM is not needed for this one.                                              *)
Lemma evalSub : forall (e:Env) (n m:nat), 
    eval e (Sub n m) <-> (e n) <= (e m).
Proof.
    intros e n m. unfold Sub. rewrite elemIncl. 
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

Lemma evalEmpty : forall (e:Env) (n:nat),
    eval e (Empty n) <-> (e n) == Nil. 
Proof.
    intros e n. unfold Empty. rewrite evalAll. split; intros H. 
    - apply emptyUnique. intros x. remember (H x) as H' eqn:E. clear E. clear H.
      rewrite evalNot in H'. rewrite evalElem in H'.
      rewrite bindSame in H'. rewrite bindDiff in H'.
        + assumption.
        + apply freshNot_n.
    - intro x. rewrite evalNot, evalElem, bindSame, bindDiff.
      rewrite emptyIsNil in H. rewrite H.
        + apply emptyCharac.
        + apply freshNot_n.
Qed.

Lemma evalMin : LEM -> forall (e:Env) (n m:nat),
    eval e (Min n m) <-> minimal (e n) (e m).
Proof.
    intros L e n m. unfold Min. rewrite evalAnd, evalElem, evalNot, evalExi.
    unfold minimal. split; intros [H1 H2].
    - split.
        + assumption.
        + intros [y H]. apply H2. exists y. rewrite evalAnd, evalElem, evalElem.
          rewrite bindSame, bindDiff, bindDiff.
            { assumption. }
            { apply freshNot_n. }
            { apply freshNot_m. }
            { assumption. }
    - split.
        + assumption.
        + intros [y H]. apply H2. exists y. rewrite evalAnd in H.
          rewrite evalElem in H. rewrite evalElem in H. rewrite bindSame in H.
          rewrite bindDiff in H. rewrite bindDiff in H.
            { assumption. }
            { apply freshNot_n. }
            { apply freshNot_m. }
            { assumption. }
    - assumption.
    - assumption.
Qed.

