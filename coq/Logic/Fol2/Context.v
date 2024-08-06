Require Import List.

Require Import Logic.List.Equiv.

Require Import Logic.Class.Eq.

Require Import Logic.List.In.
Require Import Logic.List.Include.

Require Import Logic.Fol.Syntax.
Require Import Logic.Fol.Free.

Declare Scope Fol2_Context_scope.

(* A context entry is either a variable or a proposition                        *)
Inductive CtxEntry (v:Type) : Type :=
| Var : v   -> CtxEntry v
| Prp : P v -> CtxEntry v
.

Arguments Var {v}.
Arguments Prp {v}.

(* A context is a list of context entries. No need to create a 'snoc' version   *)
(* for this, we simply need to remember new entries are 'cons'-ed to the left   *)
Definition Ctx (v: Type) : Type := list (CtxEntry v).

(* Snoc-ing a new proposition to a context                                      *)
Notation "G ; p" := (cons (Prp p) G)
  (at level 50, left associativity) : Fol2_Context_scope.

(* Snoc-ing a new variable to a context                                         *)
Notation "G , x" := (cons (Var x) G)
  (at level 50, left associativity) : Fol2_Context_scope.

Open Scope Fol2_Context_scope.

(* Free variables of a context: variables which are in scope                    *)
Fixpoint Fr' (v:Type) (e:Eq v) (G:Ctx v) : list v :=
  match G with
  | nil               => nil
  | cons (Var x) G'   => cons x (Fr' v e G')
  | cons (Prp p) G'   => Fr' v e G'
end.

Arguments Fr' {v} {e}.

(* Predicate defining a valid context                                           *)
(*                                                                              *)
(* NilCtx : the empty context is valid                                          *)
(*                                                                              *)
(* ConsV: if G is a valid context and x is not already in scope in G then       *)
(* G,x is itself a valid context                                                *)
(*                                                                              *)
(* ConsP: if G is a valid context and all free variables of p are in scope      *)
(* in G, then G;p is itself a valid context                                     *)
Inductive CtxVal (v:Type) (e:Eq v) : Ctx v -> Prop :=
| NilCtx: CtxVal v e nil
| ConsV : forall(G:Ctx v)(x:v)  ,~(x :: Fr' G) -> CtxVal v e G -> CtxVal v e (G,x)
| ConsP : forall(G:Ctx v)(p:P v),Fr p <= Fr' G -> CtxVal v e G -> CtxVal v e (G;p)
.

Arguments CtxVal {v} {e}.

Lemma validInvertP : forall (v:Type) (e:Eq v) (G:Ctx v) (p:P v),
  CtxVal (G;p) -> CtxVal G.
Proof.
  intros v e G p HVal.
  remember (G;p) as H eqn:E. revert G p E.
  destruct HVal as [ |H x HScope HVal|H q HIncl HVal].
  - intros G p A. inversion A.
  - intros G p A. inversion A.
  - intros G p A. inversion A. subst. apply HVal.
Qed.

Lemma validInvertV : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v),
  CtxVal (G,x) -> CtxVal G.
Proof.
  intros v e G x HVal.
  remember (G,x) as H eqn:E. revert G x E.
  destruct HVal as [ |H y HScope HVal|H p HIncl HVal].
  - intros G x A. inversion A.
  - intros G x A. inversion A. subst. apply HVal.
  - intros G x A. inversion A.
Qed.

Lemma validInScopeP : forall (v:Type) (e:Eq v) (G:Ctx v) (p: P v),
  CtxVal (G;p) -> Fr p <= Fr' G.
Proof.
  intros v e G p HVal.
  remember (G;p) as H eqn:E. revert G p E.
  destruct HVal as [ |H x HScope HVal|H q HIncl HVal].
  - intros G p A. inversion A.
  - intros G p A. inversion A.
  - intros G p A. inversion A. subst. apply HIncl.
Qed.

Lemma validInScopeV : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v),
  CtxVal (G,x) -> ~ (x :: Fr' G).
Proof.
  intros v e G x HVal.
  remember (G,x) as H eqn:E. revert G x E.
  destruct HVal as [ |H y HScope HVal|H p HIncl HVal].
  - intros G x A. inversion A.
  - intros G x A. inversion A. subst. apply HScope.
  - intros G x A. inversion A.
Qed.

Lemma validSwitchVNeq : forall (v:Type) (e:Eq v) (G:Ctx v) (x y:v),
  CtxVal (G,x,y) -> x <> y.
Proof.
  intros v e G x y HVal Heq. subst. apply validInScopeV in HVal.
  apply HVal. left. reflexivity.
Qed.

Lemma validSwitchV : forall (v:Type) (e:Eq v) (G:Ctx v) (x y:v),
  CtxVal (G,x,y) -> CtxVal (G,y,x).
Proof.
  intros v e G x y HVal.
  constructor.
  - intros Hx. destruct Hx as [Hx|Hx].
    + symmetry in Hx. apply validSwitchVNeq in HVal. contradiction.
    + apply validInvertV in HVal. apply validInScopeV in HVal. contradiction.
  - constructor.
    + intros Hy. apply validInScopeV in HVal. apply HVal. right. apply Hy.
    + apply validInvertV in HVal. apply validInvertV in HVal. apply HVal.
Qed.

Lemma inCtxPrp : forall (v:Type) (G:Ctx v) (x:v) (p:P v),
  Prp p :: (G,x) -> Prp p :: G.
Proof.
  intros v G x p [HIn|HIn].
  - inversion HIn.
  - apply HIn.
Qed.

Lemma inCtxSwitchV : forall (v:Type) (G:Ctx v) (x y:v) (p:P v),
  Prp p :: (G,x,y) -> Prp p :: (G,y,x).
Proof.
  intros v G x y p HIn.
  apply inCtxPrp in HIn. apply inCtxPrp in HIn.
  right. right. apply HIn.
Qed.
