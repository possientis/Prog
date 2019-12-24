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
Definition eval (p:Formula) : Prop := toProp env0 p.

(* Evaluation with single binding 'n := x'. Should be used when only 'n' free.  *)
Definition eval1 (n:nat) (x:set) (p:Formula) : Prop := toProp (env1 n x) p.

(* Evaluation with two bindings 'n := x' and 'm := y' (in that order).          *)
Definition eval2 (n m:nat)(x y:set)(p:Formula):Prop := toProp (env2 n m x y) p.

Lemma evalBot : eval Bot <-> False.
Proof. firstorder. Qed.

Lemma evalElem2 : forall (n m:nat) (x y:set), n <> m ->
    eval2 n m x y (Elem n m) <-> x :: y. 
Proof.
    intros n m x y H. unfold eval2. unfold toProp.
    rewrite env2_y. rewrite env2_x.
    - tauto.
    - assumption.
Qed.


(*

Lemma evalImp : forall (p q:Formula),
    eval (Imp p q) <-> eval p -> eval q.
Proof. firstorder. Qed.

Lemma evalAll : forall (p:Formula) (n:nat),
    eval (All n p) <-> forall (x:set), eval1 n x p.
Proof. firstorder. Qed.

Lemma evalNot : forall (p:Formula), 
    eval (Not p) <-> ~ eval p.
Proof. firstorder. Qed.

Lemma evalOr : LEM -> forall (p q:Formula), 
    eval(Or p q) <-> eval p \/ eval q.
Proof.
    intros L p q. unfold Or, eval. simpl. 
    apply LEMOr. assumption.
Qed.

Lemma evalAnd : LEM -> forall (p q:Formula),
    eval(And p q) <-> eval p /\ eval q.
Proof.
    intros L p q. unfold And, eval. simpl. 
    apply LEMAnd. assumption.
Qed.

Lemma evalExi : LEM -> forall (p:Formula) (n:nat),
    eval (Exi n p) <-> exists (x:set), eval1 n x p.
Proof.
    intros L p n. unfold Exi, eval, eval1, env1. simpl. 
    apply LEMExist. assumption.
Qed.

Definition P1 : Formula := All 0 (All 1 (Elem 0 1)).

Lemma evalP1 : eval P1 <-> forall (x y:set), x :: y.
Proof.
    firstorder.
Qed.

(* There exists an empty set                                                    *)
Definition P2 : Formula := Exi 0 (All 1 (Not (Elem 1 0))).

Lemma evalP2 : LEM -> eval P2 <-> exists (x:set), forall (z:set), ~ (z :: x).
Proof.
    intros L. apply evalExi. assumption.
Qed.

*)



