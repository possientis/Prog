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

(* Evaluation in empty environment. Should only be used for closed formulas.    *)
Definition eval (p:Formula) : Prop := toProp eDef p.

(* Evaluation with single binding 'n := x'. Should be used when only 'n' free.  *)
Definition eval_n (n:nat) (x:set) (p:Formula) : Prop := toProp (env n x) p.

Lemma checkImp : forall (p q:Formula),
    eval (Imp p q) <-> eval p -> eval q.
Proof. firstorder. Qed.

Lemma checkAll : forall (p:Formula) (n:nat),
    eval (All n p) <-> forall (x:set), eval_n n x p.
Proof. firstorder. Qed.

Lemma checkNot : forall (p:Formula), 
    eval (Not p) <-> ~ eval p.
Proof. firstorder. Qed.

Lemma checkOr : LEM -> forall (p q:Formula), 
    eval(Or p q) <-> eval p \/ eval q.
Proof.
    intros L p q. unfold Or, eval. simpl. 
    apply LEMOr. assumption.
Qed.

Lemma checkAnd : LEM -> forall (p q:Formula),
    eval(And p q) <-> eval p /\ eval q.
Proof.
    intros L p q. unfold And, eval. simpl. 
    apply LEMAnd. assumption.
Qed.

Lemma checkExi : LEM -> forall (p:Formula) (n:nat),
    eval (Exi n p) <-> exists (x:set), eval_n n x p.
Proof.
    intros L p n. unfold Exi, eval, eval_n, env. simpl. 
    apply LEMExist. assumption.
Qed.

Definition P1 : Formula := All 0 (All 1 (Elem 0 1)).

Lemma checkP1 : eval P1 <-> forall (x y:set), x :: y.
Proof.
    firstorder.
Qed.

(* There exists an empty set                                                    *)
Definition P2 : Formula := Exi 0 (All 1 (Not (Elem 1 0))).

Lemma checkP2 : LEM -> eval P2 <-> exists (x:set), forall (z:set), ~ (z :: x).
Proof.
    intros L. apply checkExi. assumption.
Qed.





