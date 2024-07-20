Require Import Logic.Fol.Syntax.
Require Import Logic.Fol2.Context.
Require Import Logic.Fol2.Axiom.

Declare Scope Fol2_Proof_scope.

Inductive Seq (v:Type) : Ctx v -> P v -> Type :=
| Extract:forall (G:Ctx v)(p:P v),     Seq v (G;p) p 
| WeakenP:forall (G:Ctx v)(p q:P v),   Seq v G p -> Seq v (G;q) p
| WeakenV:forall (G:Ctx v)(x:v)(p:P v),Seq v G p -> Seq v (G,x) p
| Deduct: forall (G:Ctx v)(p q:P v),   Seq v (G;p) q -> Seq v G (p :-> q)
| Modus:  forall (G:Ctx v)(p q: P v),  Seq v G p -> Seq v G (p :-> q) -> Seq v G q
| Reduct: forall (G:Ctx v)(p:P v),     Seq v (G;¬p) bot -> Seq v G p
.

 
