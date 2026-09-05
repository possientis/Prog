Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Syntax.

Fixpoint fromT (i:nat) (r:nat -> Term) (t:Term) : Term :=
  match t with
  | Bot              => Bot
  | Top              => Top
  | Var n            => if n <? i then Var n else shiftT i (r (n - i))
  | HoleT ty         => HoleT ty
  | IdentT name args => IdentT name (fromTs i r args)
  | Elem x y         => Elem  (fromT i r x) (fromT i r y)
  | Leq x y          => Leq   (fromT i r x) (fromT i r y)
  | Geq x y          => Geq   (fromT i r x) (fromT i r y)
  | Lt x y           => Lt    (fromT i r x) (fromT i r y)
  | Gt x y           => Gt    (fromT i r x) (fromT i r y)
  | Equal x y        => Equal (fromT i r x) (fromT i r y)
  | NotEq x y        => NotEq (fromT i r x) (fromT i r y)
  | Imp p q          => Imp   (fromT i r p) (fromT i r q)
  | Iff p q          => Iff   (fromT i r p) (fromT i r q)
  | And p q          => And   (fromT i r p) (fromT i r q)
  | Or p q           => Or    (fromT i r p) (fromT i r q)
  | Not p            => Not   (fromT i r p)
  | All p            => All   (fromT (S i) r p)
  | Ex p             => Ex    (fromT (S i) r p)
  | Lam p            => Lam   (fromT (S i) r p)
  | App A x          => App   (fromT i r A) (fromT i r x)
  | Def A p q        => Def   (fromT i r A) (fromP i r p) (fromP i r q)
  end
with fromP (i:nat) (r:nat -> Term) (p:Proof) : Proof :=
  match p with
  | HoleP t        => HoleP (fromT i r t)
  | AxiomP t       => AxiomP (fromT i r t)
  | IdentP name ts => IdentP name (fromTs i r ts)
  end
with fromTs (i:nat) (r:nat -> Term) (ts:Terms) : Terms :=
  match ts with
  | NilT       => NilT
  | ConsT t ts => ConsT (fromT i r t) (fromTs i r ts)
  end.

Definition substT (r:nat -> Term) (t:Term)  : Term := fromT 0 r t.

Definition substP (r:nat -> Term) (p:Proof) : Proof := fromP 0 r p.
