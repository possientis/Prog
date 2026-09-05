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
