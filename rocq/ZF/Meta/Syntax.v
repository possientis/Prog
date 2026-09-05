Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Inductive Term : Type :=
(* Logical constants.                                                           *)
| Bot     : Term
| Top     : Term
(* Local variables and typed incomplete terms.                                  *)
| Var     : nat    -> Term
| HoleT   : Ty     -> Term
(* A named term declaration applied to all its ordinary arguments.              *)
| IdentT  : Name   -> Terms -> Term
(* Set-theoretic atomic propositions and comparison forms.                      *)
| Elem    : Term   -> Term      -> Term
| Leq     : Term   -> Term      -> Term
| Geq     : Term   -> Term      -> Term
| Lt      : Term   -> Term      -> Term
| Gt      : Term   -> Term      -> Term
| Equal   : Term   -> Term      -> Term
| NotEq   : Term   -> Term      -> Term
(* Propositional connectives.                                                   *)
| Imp     : Term   -> Term      -> Term
| Iff     : Term   -> Term      -> Term
| And     : Term   -> Term      -> Term
| Or      : Term   -> Term      -> Term
| Not     : Term   -> Term
(* Quantifiers bind one set variable.                                           *)
| All     : Term   -> Term
| Ex      : Term   -> Term
(* A class abstraction binds one set variable.                                  *)
| Lam     : Term   -> Term
(* Class application forms a proposition.                                       *)
| App     : Term   -> Term      -> Term
(* A definition term packages a class with existence and uniqueness proofs.     *)
| Def     : Term   -> Proof     -> Proof     -> Term
with Proof : Type :=
(* An incomplete proof reference for a proposition.                             *)
| HoleP  : Term    -> Proof
(* An axiomatic proof reference for a proposition.                              *)
| AxiomP : Term    -> Proof
(* A named proof declaration applied to all its ordinary arguments.             *)
| IdentP : Name    -> Terms -> Proof
with Terms : Type :=
(* The empty list of ordinary term arguments.                                   *)
| NilT   : Terms
(* A non-empty list of ordinary term arguments.                                 *)
| ConsT  : Term    -> Terms -> Terms
.

Fixpoint fromList (ts:list Term) : Terms :=
  match ts with
  | []      => NilT
  | t :: ts => ConsT t (fromList ts)
  end.

Fixpoint toList (ts:Terms) : list Term :=
  match ts with
  | NilT       => []
  | ConsT t ts => t :: toList ts
  end.

#[warnings="-uniform-inheritance"]
Coercion fromList : list >-> Terms.

Definition lengthT (ts:Terms) : nat := List.length (toList ts).

Definition nthT (ts:Terms) (n:nat) : option Term := nth_error (toList ts) n.

Fixpoint appT (ts us:Terms) : Terms :=
  match ts with
  | NilT       => us
  | ConsT t ts => ConsT t (appT ts us)
  end.

Fixpoint revT (ts:Terms) : Terms :=
  match ts with
  | NilT       => NilT
  | ConsT t ts => appT (revT ts) (ConsT t NilT)
  end.

(* Converting an ordinary list to term arguments and back changes nothing.      *)
Proposition ToListFromList : forall (ts:list Term),
    toList (fromList ts) = ts.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts.
  induction ts as [|t ts IH]. 1: reflexivity.
  simpl. rewrite IH. reflexivity.
Qed.

(* Converting appended term arguments gives the appended ordinary lists.        *)
Proposition ToListAppT : forall (ts us:Terms),
    toList (appT ts us) = List.app (toList ts) (toList us).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts us.
  induction ts as [|t ts IH]. 1: reflexivity.
  simpl. rewrite IH. reflexivity.
Qed.

(* Converting reversed term arguments gives the reversed ordinary list.         *)
Proposition ToListRevT : forall (ts:Terms),
    toList (revT ts) = rev (toList ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts.
  induction ts as [|t ts IH]. 1: reflexivity.
  simpl. rewrite ToListAppT, IH. reflexivity.
Qed.
