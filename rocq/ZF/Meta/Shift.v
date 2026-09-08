Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Induction.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

(* De Bruijn lifting raises free variables by j at or above a level i.          *)
Fixpoint fromT (i j:nat) (t:Term) : Term :=
  match t with
  | Bot              => Bot
  | Top              => Top
  | Var n            => if n <? i then Var n else Var (n + j)
  | HoleT ty         => HoleT ty
  | IdentT name args => IdentT name (fromTs i j args)
  | Elem x y         => Elem  (fromT i j x) (fromT i j y)
  | Leq x y          => Leq   (fromT i j x) (fromT i j y)
  | Geq x y          => Geq   (fromT i j x) (fromT i j y)
  | Lt x y           => Lt    (fromT i j x) (fromT i j y)
  | Gt x y           => Gt    (fromT i j x) (fromT i j y)
  | Equal x y        => Equal (fromT i j x) (fromT i j y)
  | NotEq x y        => NotEq (fromT i j x) (fromT i j y)
  | Imp p q          => Imp   (fromT i j p) (fromT i j q)
  | Iff p q          => Iff   (fromT i j p) (fromT i j q)
  | And p q          => And   (fromT i j p) (fromT i j q)
  | Or p q           => Or    (fromT i j p) (fromT i j q)
  | Not p            => Not   (fromT i j p)
  | All p            => All   (fromT (S i) j p)
  | Ex p             => Ex    (fromT (S i) j p)
  | Lam p            => Lam   (fromT (S i) j p)
  | App A x          => App   (fromT i j A) (fromT i j x)
  | Def A p q        => Def   (fromT i j A) (fromP i j p) (fromP i j q)
  end
with fromP (i j:nat) (p:Proof) : Proof :=
  match p with
  | HoleP t        => HoleP (fromT i j t)
  | AxiomP t       => AxiomP (fromT i j t)
  | IdentP name ts => IdentP name (fromTs i j ts)
  end
with fromTs (i j:nat) (ts:Terms) : Terms :=
  match ts with
  | NilT       => NilT
  | ConsT t ts => ConsT (fromT i j t) (fromTs i j ts)
  end.

(* De Bruijn lifting raises every free variable in a term by n.                 *)
Definition shiftT (n:nat) (t:Term) : Term := fromT 0 n t.

(* De Bruijn lifting raises every free variable in a proof by n.                *)
Definition shiftP (n:nat) (p:Proof) : Proof := fromP 0 n p.

Proposition WhenZero :
  (forall (t:Term)   (i:nat), fromT   i 0 t  = t)     /\
  (forall (p:Proof)  (i:nat), fromP   i 0 p  = p)     /\
  (forall (ts:Terms) (i:nat), fromTs  i 0 ts = ts).
Proof.
  apply Induction.
  - intros i. reflexivity.
  - intros i. reflexivity.
  - intros n i. simpl.
    destruct (n <? i). 1: reflexivity. rewrite Nat.add_0_r. reflexivity.
  - intros ty i. reflexivity.
  - intros name args IH i. simpl. rewrite IH. reflexivity.
  - intros x y IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros p IH i. simpl. rewrite IH. reflexivity.
  - intros p IH i. simpl. rewrite IH. reflexivity.
  - intros p IH i. simpl. rewrite IH. reflexivity.
  - intros p IH i. simpl. rewrite IH. reflexivity.
  - intros A x IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
  - intros A p q IH1 IH2 IH3 i. simpl. rewrite IH1, IH2, IH3. reflexivity.
  - intros t IH i. simpl. rewrite IH. reflexivity.
  - intros t IH i. simpl. rewrite IH. reflexivity.
  - intros name args IH i. simpl. rewrite IH. reflexivity.
  - intros i. reflexivity.
  - intros t ts IH1 IH2 i. simpl. rewrite IH1, IH2. reflexivity.
Qed.

(* Lifting a term by zero leaves it unchanged.                                  *)
Proposition ShiftZeroT : forall (t:Term),
    shiftT 0 t = t.
Proof.
  intros t. apply WhenZero.
Qed.


(* A later lifting commutes with an earlier lifting at a lower cutoff.          *)
Proposition Comm :
  (forall (t:Term) (i j k l:nat), i <= k ->
    fromT (k + j) l (fromT i j t) = fromT i j (fromT k l t))          /\
  (forall (p:Proof) (i j k l:nat), i <= k ->
    fromP (k + j) l (fromP i j p) = fromP i j (fromP k l p))          /\
  (forall (ts:Terms) (i j k l:nat), i <= k ->
    fromTs (k + j) l (fromTs i j ts) = fromTs i j (fromTs k l ts)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Induction.
  - intros i j k l H1. reflexivity.
  - intros i j k l H1. reflexivity.
  - intros n i j k l H1. simpl.
    (* A variable below the first cutoff is below both later cutoffs.           *)
    destruct (n <? i) eqn:H2.
    + apply Nat.ltb_lt in H2.
      assert (n < k) as H3. {
        apply Nat.lt_le_trans with (m := i); assumption. }
      assert ((n <? k) = true) as H4. { apply Nat.ltb_lt. assumption. }
      assert (n < k + j) as H5. {
        apply Nat.lt_le_trans with (m := k).
        1: assumption.
        apply Nat.le_add_r. }
      assert ((n <? k + j) = true) as H6. { apply Nat.ltb_lt. assumption. }
      assert ((n <? i) = true) as H7. { apply Nat.ltb_lt. assumption. }
      simpl. rewrite H6. simpl. rewrite H4. simpl. rewrite H7. reflexivity.
    + apply Nat.ltb_ge in H2.
      (* A remaining variable is either between the cutoffs or after both.      *)
      destruct (n <? k) eqn:H3.
      * apply Nat.ltb_lt in H3.
        assert (n + j < k + j) as H4. {
          apply Nat.add_lt_mono_r. assumption. }
        assert ((n + j <? k + j) = true) as H5. {
          apply Nat.ltb_lt. assumption. }
        assert ((n <? i) = false) as H6. { apply Nat.ltb_ge. assumption. }
        simpl. rewrite H5. simpl. rewrite H6. reflexivity.
      * apply Nat.ltb_ge in H3.
        assert (k + j <= n + j) as H4. {
          apply Nat.add_le_mono_r. assumption. }
        assert ((n + j <? k + j) = false) as H5. {
          apply Nat.ltb_ge. assumption. }
        assert (i <= n + l) as H6. {
          apply Nat.le_trans with (m := k).
          1: assumption.
          apply Nat.le_trans with (m := n).
          1: assumption.
          apply Nat.le_add_r. }
        assert ((n + l <? i) = false) as H7. { apply Nat.ltb_ge. assumption. }
        simpl. rewrite H5. simpl. rewrite H7.
        assert (n + j + l = n + l + j) as H8. {
          rewrite <- Nat.add_assoc.
          rewrite (Nat.add_comm j l).
          rewrite Nat.add_assoc. reflexivity. }
        rewrite H8. reflexivity.
  - intros ty i j k l H1. reflexivity.
  - intros name args IH i j k l H1. simpl. rewrite IH. reflexivity. assumption.
  - intros x y IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros x y IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros x y IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros x y IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros x y IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros x y IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros x y IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros p q IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros p q IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros p q IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros p q IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros p IH i j k l H1. simpl. rewrite IH. reflexivity. assumption.
  - intros p IH i j k l H1. simpl.
    (* Under a binder both cutoffs advance by one, preserving their order.      *)
    assert (S (k + j) = S k + j) as H2. { reflexivity. }
    rewrite H2. rewrite IH. 2: apply le_n_S; assumption. reflexivity.
  - intros p IH i j k l H1. simpl.
    assert (S (k + j) = S k + j) as H2. { reflexivity. }
    rewrite H2. rewrite IH. 2: apply le_n_S; assumption. reflexivity.
  - intros p IH i j k l H1. simpl.
    assert (S (k + j) = S k + j) as H2. { reflexivity. }
    rewrite H2. rewrite IH. 2: apply le_n_S; assumption. reflexivity.
  - intros A x IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
  - intros A p q IH1 IH2 IH3 i j k l H1. simpl.
    rewrite IH1, IH2, IH3; try assumption. reflexivity.
  - intros t IH i j k l H1. simpl. rewrite IH. reflexivity. assumption.
  - intros t IH i j k l H1. simpl. rewrite IH. reflexivity. assumption.
  - intros name ts IH i j k l H1. simpl. rewrite IH. reflexivity. assumption.
  - intros i j k l H1. reflexivity.
  - intros t ts IH1 IH2 i j k l H1. simpl.
    rewrite IH1, IH2; try assumption. reflexivity.
Qed.

(* A later lifting commutes with an earlier lifting in terms.                   *)
Proposition CommT : forall (t:Term) (i j k l:nat), i <= k ->
  fromT (k + j) l (fromT i j t) = fromT i j (fromT k l t).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Comm.
Qed.

(* A later lifting commutes with an earlier lifting in proofs.                  *)
Proposition CommP : forall (p:Proof) (i j k l:nat), i <= k ->
  fromP (k + j) l (fromP i j p) = fromP i j (fromP k l p).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Comm.
Qed.

(* A later lifting commutes with an earlier lifting in term arguments.          *)
Proposition CommTs : forall (ts:Terms) (i j k l:nat), i <= k ->
  fromTs (k + j) l (fromTs i j ts) = fromTs i j (fromTs k l ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Comm.
Qed.

(* Lifting above an earlier lifting combines with the earlier lifting.          *)
Proposition Add :
  (forall (t:Term) (i j k l:nat),
    fromT (i + j) k (fromT i (j + l) t) = fromT i (j + k + l) t)          /\
  (forall (p:Proof) (i j k l:nat),
    fromP (i + j) k (fromP i (j + l) p) = fromP i (j + k + l) p)          /\
  (forall (ts:Terms) (i j k l:nat),
    fromTs (i + j) k (fromTs i (j + l) ts) = fromTs i (j + k + l) ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Induction.
  - intros i j k l. reflexivity.
  - intros i j k l. reflexivity.
  - intros n i j k l. simpl.
    (* Variables below the earlier cutoff remain below the later cutoff.        *)
    destruct (n <? i) eqn:H1.
    + apply Nat.ltb_lt in H1.
      assert ((n <? i + j) = true) as H2. {
        apply Nat.ltb_lt.
        apply Nat.lt_le_trans with (m := i).
        1: assumption.
        apply Nat.le_add_r. }
      simpl. rewrite H2. reflexivity.
    + apply Nat.ltb_ge in H1.
      assert ((n + (j + l) <? i + j) = false) as H2. {
        apply Nat.ltb_ge.
        apply Nat.add_le_mono; try assumption.
        apply Nat.le_add_r. }
      simpl. rewrite H2.
      assert (n + (j + l) + k = n + (j + k + l)) as H4. {
        rewrite <- Nat.add_assoc.
        assert (j + l + k = j + k + l) as H4. {
          rewrite <- Nat.add_assoc.
          rewrite (Nat.add_comm l k).
          rewrite Nat.add_assoc. reflexivity. }
        rewrite H4. reflexivity. }
      rewrite H4. reflexivity.
  - intros ty i j k l. reflexivity.
  - intros name args IH i j k l. simpl. rewrite IH. reflexivity.
  - intros x y IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros p IH i j k l. simpl. rewrite IH. reflexivity.
  - intros p IH i j k l. simpl.
    assert (S (i + j) = S i + j) as H1. { reflexivity. }
    rewrite H1. rewrite IH. reflexivity.
  - intros p IH i j k l. simpl.
    assert (S (i + j) = S i + j) as H1. { reflexivity. }
    rewrite H1. rewrite IH. reflexivity.
  - intros p IH i j k l. simpl.
    assert (S (i + j) = S i + j) as H1. { reflexivity. }
    rewrite H1. rewrite IH. reflexivity.
  - intros A x IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
  - intros A p q IH1 IH2 IH3 i j k l. simpl.
    rewrite IH1, IH2, IH3. reflexivity.
  - intros t IH i j k l. simpl. rewrite IH. reflexivity.
  - intros t IH i j k l. simpl. rewrite IH. reflexivity.
  - intros name ts IH i j k l. simpl. rewrite IH. reflexivity.
  - intros i j k l. reflexivity.
  - intros t ts IH1 IH2 i j k l. simpl. rewrite IH1, IH2. reflexivity.
Qed.

(* Lifting above an already full-lifted term gives another full lifting.        *)
Proposition FromShiftT : forall (t:Term) (i j k:nat),
  fromT i j (shiftT (i + k) t) = shiftT (i + j + k) t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros t i j k. unfold shiftT.
  assert (0 + i = i) as H1. { reflexivity. }
  rewrite <- H1. apply Add.
Qed.
