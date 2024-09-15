Require Import Logic.Prop.Syntax.
Require Import Logic.Prop.Context.

Declare Scope Prop_CutElim_scope.

(* Same as Seq but without modus ponens *)
Inductive Seq' (v:Type) : Ctx v -> P v -> Type :=
| FromHyp':forall (G:Ctx v)(p:P v),    Seq' v (G;p) p
| Weaken': forall (G:Ctx v)(p q:P v),  Seq' v G p -> Seq' v (G;q) p
| Switch': forall (G:Ctx v)(p q r:P v),Seq' v (G;p;q) r -> Seq' v (G;q;p) r
| Deduct': forall (G:Ctx v)(p q:P v),  Seq' v (G;p) q -> Seq' v G (p :-> q)
| Apply' : forall (G:Ctx v)(p q:P v),  Seq' v G (p :-> q) -> Seq' v (G;p) q
| Reduct': forall (G:Ctx v)(p:P v),    Seq' v (G;¬p) bot -> Seq' v G p
.

Arguments Seq'     {v}.
Arguments FromHyp' {v}.
Arguments Weaken'  {v}.
Arguments Switch'  {v}.
Arguments Deduct'  {v}.
Arguments Apply'   {v}.
Arguments Reduct'  {v}.

Notation "G #- p" := (Seq' G p)
  (at level 90, no associativity) : Prop_CutElim_scope.

Open Scope Prop_CutElim_scope.

Definition cutElim (v:Type) (G:Ctx v) (p q:P v) (e:G #- p) (e':G;p #- q) : G #- q.
Proof.
  remember (G;p) as H eqn:E. revert E.
  induction e' as
    [H p'
    |H p' q' e' IH
    |H p' q' r' e' IH
    |H p' q' e' IH
    |H p' q' e' IH
    |H p' e' IH
    ]; intros E.
  - inversion E. subst. exact e.
  - inversion E. subst. exact e'.
  - inversion E. clear E.


Show.
