Require Import Logic.Class.Eq.

Require Import Logic.Func.Permute.

Require Import Logic.List.In.
Require Import Logic.List.Include.


Require Import Logic.Fol.Free.
Require Import Logic.Fol.Functor.
Require Import Logic.Fol.Syntax.

Require Import Logic.Fol2.Context.
Require Import Logic.Fol2.Axiom.

Declare Scope Fol2_Proof_scope.

Inductive Seq (v:Type) (e:Eq v) : Ctx v -> P v -> Type :=
| Extract:forall (G:Ctx v)(p:P v),      CtxVal G -> Fr p <= Fr' G -> Seq v e (G;p) p 
| WeakenV:forall (G:Ctx v)(x:v)(p:P v), ~(x :: Fr' G) -> Seq v e G p -> Seq v e (G,x) p
| WeakenP:forall (G:Ctx v)(p q:P v),    Fr q <= Fr' G -> Seq v e G p -> Seq v e (G;q) p
| Deduct :forall (G:Ctx v)(p q:P v),    Seq v e (G;p) q -> Seq v e G (p :-> q)
| Modus  :forall (G:Ctx v)(p q: P v),   Seq v e G p -> Seq v e G (p :-> q) -> Seq v e G q
| Reduct :forall (G:Ctx v)(p:P v),      Seq v e (G;¬p) bot -> Seq v e G p
| AxiomP :forall (G:Ctx v)(p:P v),      CtxVal G -> IsAxiom p -> Seq v e G p 
| General:forall (G:Ctx v)(x:v)(p:P v), Seq v e (G,x) p -> Seq v e G (All x p) 
| Special:forall (G:Ctx v)(x y:v)(p:P v),
    CtxVal G              ->
    Fr (All x p) <= Fr' G ->
    ~ (y :: Fr' G)        -> 
    Seq v e (G;All x p,y) (fmap (y <:> x) p)
.

Arguments Seq     {v} {e}.
Arguments Extract {v} {e}.
Arguments WeakenV {v} {e}.
Arguments WeakenP {v} {e}.
Arguments Deduct  {v} {e}.
Arguments Modus   {v} {e}.
Arguments Reduct  {v} {e}.
Arguments AxiomP  {v} {e}.
Arguments General {v} {e}.
Arguments Special {v} {e}.

Notation "G :- p" := (Seq G p)
  (at level 90, no associativity) : Fol2_Proof_scope.

Open Scope Fol2_Proof_scope.
