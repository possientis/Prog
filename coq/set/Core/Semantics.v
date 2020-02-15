Require Import List.
Require Import Peano_dec.
Require Import PeanoNat.
Import Nat.

Require Import Core.LEM.
Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Empty.
Require Import Core.Fresh.
Require Import Core.Syntax.
Require Import Core.ElemIncl.
Require Import Core.Foundation.
Require Import Core.Environment.

Fixpoint eval (e:Env) (p:Formula) : Prop :=
    match p with
    | Bot           => False
    | Elem n m      => (e n) :: (e m)
    | Imp p1 p2     => eval e p1 -> eval e p2
    | All n p1      => forall (x:set), eval (bind e n x) p1
    end.

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

Lemma relevance : forall (e e':Env) (p:Formula), 
    envEqualOn p e e' -> eval e p <-> eval e' p.
Proof.
    intros e e' p. unfold envEqualOn. revert e e'.
    induction p as [|n m|p1 IH1 p2 IH2|n p1 IH1]; intros e e' H; simpl.
    - tauto.
    - split. 
        + apply equal_lr; apply H.
            { left. reflexivity. }
            { right. left. reflexivity. }
        + apply equal_lr; apply equalSym; apply H.
            { left. reflexivity. }
            { right. left. reflexivity. }
    - rewrite (IH1 e e'), (IH2 e e').
        + tauto.
        + intros n H'. apply H. simpl. apply in_or_app. right. assumption.
        + intros n H'. apply H. simpl. apply in_or_app. left.  assumption.
    - split; intros H' x.
        + rewrite (IH1 (bind e' n x) (bind e n x)). 
            { apply H'. }
            { intros m.  destruct (eq_nat_dec n m) as [E|E].
                { subst. rewrite bindSame, bindSame. intros. apply equalRefl. }
                { rewrite bindDiff, bindDiff.
                    { intros H''. apply equalSym. apply H. simpl. 
                      apply removeStill; assumption. }
                    { assumption. }
                    { assumption. }}}
        + rewrite (IH1 (bind e n x) (bind e' n x)). 
            { apply H'. }
            { intros m H''. destruct (eq_nat_dec n m) as [E|E].
                { subst. rewrite bindSame, bindSame. apply equalRefl. }
                { rewrite bindDiff, bindDiff.
                    { apply H. simpl. apply removeStill; assumption. }
                    { assumption. }
                    { assumption. }}}
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

Lemma evalEnvEqual : forall (e e':Env) (p:Formula),
    envEqual e e' -> eval e p <-> eval e' p.
Proof.
    intros e e' p H. apply relevance. intros n H'. apply H.
Qed.


Lemma evalNotInFree : forall (e:Env) (n:nat) (x:set) (p:Formula),
    ~In n (free p) -> eval (bind e n x) p <-> eval e p.
Proof.
    intros e n x p H. apply relevance. intros m H'. 
    destruct (eq_nat_dec n m) as [E|E].
    - subst. apply H in H'. contradiction.
    - rewrite bindDiff. 
        + apply equalRefl.
        + assumption.
Qed.
