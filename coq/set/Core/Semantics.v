Require Import Core.LEM.
Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Syntax.
Require Import Core.Environment.

Fixpoint toProp (e:Env) (p:Formula) : Prop :=
    match p with
    | Bot           => False
    | Elem n m      => (e n) :: (e m)
    | Imp p1 p2     => toProp e p1 -> toProp e p2
    | All n p1      => forall (x:set), toProp (bind e n x) p1
    end.

(* Evaluation is empty environment. Should only be used for closed formulas.    *)
Definition eval (p:Formula) : Prop := toProp eDef p.

(* Evaluation with single binding 'n := x'. Should be used when only 'n' free.  *)
Definition eval_n (n:nat) (x:set) (p:Formula) : Prop := toProp (env n x) p.

Definition p1 : Formula := All 0 (All 1 (Elem 0 1)).

Ltac ceval :=
    unfold eval, toProp, eDef, bind, eq_nat_dec; simpl.

Lemma L1 : eval p1 <-> forall (x y:set), x :: y.
Proof.
    unfold p1. ceval. firstorder.
Qed.

Lemma checkNot : forall (p:Formula), 
    eval (Not p) <-> ~ eval p.
Proof. firstorder. Qed.

Lemma checkOr : LEM -> forall (p q:Formula), 
    eval(Or p q) <-> eval p \/ eval q.
Proof.
    intros L p q. unfold Or, eval. simpl. 
    apply LEMor. assumption.
Qed.

Lemma checkAnd : LEM -> forall (p q:Formula),
    eval(And p q) <-> eval p /\ eval q.
Proof.
    intros L p q. unfold And, eval. simpl. 
    apply LEMAnd. assumption.
Qed.

Lemma checkExist : LEM -> forall (p:Formula) (n:nat),
    eval (Exist n p) <-> exists (x:set), eval_n n x p.
Proof.
    intros L p n. unfold Exist, eval, eval_n, env. simpl. 
    apply LEMExist. assumption.
Qed.

Lemma checkImp : forall (p q:Formula),
    eval (Imp p q) <-> eval p -> eval q.
Proof. firstorder. Qed.

Lemma checkForall : forall (p:Formula) (n:nat),
    eval (All n p) <-> forall (x:set), eval_n n x p.
Proof. firstorder. Qed.

