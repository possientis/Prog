Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Syntax.

(* De Bruijn lifting raises free variables by j at or above a level i.          *)
Fixpoint FromT (i j:nat) (t:Term) : Term :=
  match t with
  | Bot              => Bot
  | Top              => Top
  | Var n            => if n <? i then Var n else Var (n + j)
  | HoleT ty         => HoleT ty
  | IdentT name args => IdentT name (map (FromT i j) args)
  | Elem x y         => Elem  (FromT i j x) (FromT i j y)
  | Leq x y          => Leq   (FromT i j x) (FromT i j y)
  | Geq x y          => Geq   (FromT i j x) (FromT i j y)
  | Lt x y           => Lt    (FromT i j x) (FromT i j y)
  | Gt x y           => Gt    (FromT i j x) (FromT i j y)
  | Equal x y        => Equal (FromT i j x) (FromT i j y)
  | NotEq x y        => NotEq (FromT i j x) (FromT i j y)
  | Imp p q          => Imp   (FromT i j p) (FromT i j q)
  | Iff p q          => Iff   (FromT i j p) (FromT i j q)
  | And p q          => And   (FromT i j p) (FromT i j q)
  | Or p q           => Or    (FromT i j p) (FromT i j q)
  | Not p            => Not   (FromT i j p)
  | All p            => All   (FromT (S i) j p)
  | Ex p             => Ex    (FromT (S i) j p)
  | Lam p            => Lam   (FromT (S i) j p)
  | App A x          => App   (FromT i j A) (FromT i j x)
  | Def A p q        => Def   (FromT i j A) (FromP i j p) (FromP i j q)
  end
with FromP (i j:nat) (p:Proof) : Proof :=
  match p with
  | HoleP t        => HoleP (FromT i j t)
  | AxiomP t       => AxiomP (FromT i j t)
  | IdentP name ts => IdentP name (map (FromT i j) ts)
  end.

(* De Bruijn lifting raises every free variable in a term by n.                 *)
Definition ShiftT (n:nat) (t:Term) : Term := FromT 0 n t.

(* De Bruijn lifting raises every free variable in a proof by n.                *)
Definition ShiftP (n:nat) (p:Proof) : Proof := FromP 0 n p.
