Require Import List.

Declare Scope Prop_Syntax_scope.

(* Given a type v of all propositional variables, defines the tyoe P v of all   *)
(* formulas of propositional logic with atoms in v                              *)
Inductive P (v:Type) : Type :=
| Bot : P v
| Var : v -> P v
| Imp : P v -> P v -> P v
.

Arguments Bot {v}.
Arguments Var {v}.
Arguments Imp {v}.

(* A context is a list of propositions. No need to create a 'snoc' version for  *)
(* this, we simply need to remember new formulas are 'cons'-ed to the left      *)
Definition Ctx (v: Type) : Type := list (P v).

Notation "ctx ; p" := (cons p ctx)
    (at level 50, left associativity) : Prop_Syntax_scope.
     
Open Scope Prop_Syntax_scope.

(* Extract: construct a proof of the sequent ctx;p :- p                         *)
(* So that a formula p is provable from a context with p itself as its head     *)
(*                                                                              *)
(* Deduct: given a proof of the sequent ctx ; p :- q , provides a proof of the  *)
(* sequent ctx :- p -> q. So p -> q is provable in context ctx if q is provable *)
(* in context ctx;p                                                             *)
(*                                                                              *)
(* Modus : aka modus ponens, combines a proof of the sequent ctx :- p and a     *)
(* proof of the sequent ctx :- p -> q to create a proof of the sequent ctx :- q *)
(* So q is provable under ctx if both p and p -> q are                          *)
(*                                                                              *)
(* Reduct: aka RAA or Reductio ad absurdum, creates a proof of the sequent      *)
(* ctx :- p from a proof of the sequent ctx;¬p :- Bot                           *)
(* So if bottom is provable from a context ctx, having assumed ¬p, then p is    *)
(* provable from the context ctx                                                *)
(*                                                                              *)
(* Weaken: creates a proof of ctx;q :- p from a prroof of ctx :- p              *)
(* So if p is provable under ctx, it is provable under the larger context ctx;q *)

Inductive Seq (v:Type) : Ctx v -> P v -> Type :=
| Extract : forall (ctx:Ctx v) (p:P v), Seq v (ctx;p) p 
| Deduct : forall (ctx:Ctx v) (p q:P v), Seq v (ctx;p) q -> Seq v ctx (Imp p q)
| Modus : forall (ctx:Ctx v) (p q: P v), 
  Seq v ctx p -> Seq v ctx (Imp p q) -> Seq v ctx q
| Reduct: forall (ctx:Ctx v) (p:P v), Seq v (ctx;Imp p Bot) Bot -> Seq v ctx p
| Weaken: forall (ctx:Ctx v) (p q:P v), Seq v ctx p -> Seq v (ctx;q) p
.
