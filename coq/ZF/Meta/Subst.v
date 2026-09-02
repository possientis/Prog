Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Syntax.

Fixpoint FromT (i:nat) (r:nat -> Term) (t:Term) : Term :=
  match t with
  | Bot              => Bot
  | Top              => Top
  | Var n            => if n <? i then Var n else ShiftT i (r (n - i))
  | HoleT ty         => HoleT ty
  | IdentT name args => IdentT name (map (FromT i r) args)
  | Elem x y         => Elem  (FromT i r x) (FromT i r y)
  | Leq x y          => Leq   (FromT i r x) (FromT i r y)
  | Geq x y          => Geq   (FromT i r x) (FromT i r y)
  | Lt x y           => Lt    (FromT i r x) (FromT i r y)
  | Gt x y           => Gt    (FromT i r x) (FromT i r y)
  | Equal x y        => Equal (FromT i r x) (FromT i r y)
  | NotEq x y        => NotEq (FromT i r x) (FromT i r y)
  | Imp p q          => Imp   (FromT i r p) (FromT i r q)
  | Iff p q          => Iff   (FromT i r p) (FromT i r q)
  | And p q          => And   (FromT i r p) (FromT i r q)
  | Or p q           => Or    (FromT i r p) (FromT i r q)
  | Not p            => Not   (FromT i r p)
  | All p            => All   (FromT (S i) r p)
  | Ex p             => Ex    (FromT (S i) r p)
  | Lam p            => Lam   (FromT (S i) r p)
  | App A x          => App   (FromT i r A) (FromT i r x)
  | Def A p q        => Def   (FromT i r A) (FromP i r p) (FromP i r q)
  end
with FromP (i:nat) (r:nat -> Term) (p:Proof) : Proof :=
  match p with
  | HoleP t        => HoleP (FromT i r t)
  | AxiomP t       => AxiomP (FromT i r t)
  | IdentP name ts => IdentP name (map (FromT i r) ts)
  end.

Definition SubstT (r:nat -> Term) (t:Term)  : Term := FromT 0 r t.

Definition SubstP (r:nat -> Term) (p:Proof) : Proof := FromP 0 r p.
