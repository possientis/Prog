Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Syntax.

(* De Bruijn lifting raises free variables by j at or above a level i.          *)
Fixpoint fromT (i j:nat) (t:Term) : Term :=
  match t with
  | Bot              => Bot
  | Top              => Top
  | Var n            => if n <? i then Var n else Var (n + j)
  | HoleT ty         => HoleT ty
  | IdentT name args => IdentT name (map (fromT i j) args)
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
  | IdentP name ts => IdentP name (map (fromT i j) ts)
  end.

(* De Bruijn lifting raises every free variable in a term by n.                 *)
Definition shiftT (n:nat) (t:Term) : Term := fromT 0 n t.

(* De Bruijn lifting raises every free variable in a proof by n.                *)
Definition shiftP (n:nat) (p:Proof) : Proof := fromP 0 n p.
