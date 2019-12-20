Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.LEM.
Require Import Core.Elem.
Require Import Core.Formula.


Definition Env : Type := nat -> set.

Definition eDef : Env := (fun _ => Nil).

(* Tweak environment e to that e n = x                                          *)
Definition bind (e:Env) (n:nat) (x:set) : Env :=
    fun (m:nat) =>
        match eq_nat_dec n m with
        | left _    => x        (* variable 'n' is bound to set 'x'             *)
        | right _   => e m
        end.

Fixpoint toProp (e:Env) (p:Formula) : Prop :=
    match p with
    | Bot           => False
    | Elem n m      => (e n) :: (e m)
    | Imp p1 p2     => toProp e p1 -> toProp e p2
    | All n p1      => forall (x:set), toProp (bind e n x) p1
    end.

Definition eval (p:Formula) : Prop := toProp eDef p.

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
    intros L p q. unfold Or, eval. simpl. apply LEMor. assumption.
Qed.

