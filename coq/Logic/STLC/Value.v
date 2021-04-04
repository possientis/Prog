Require Import Logic.STLC.Syntax.

(* Predicates defining terms which are neutral and are values in STLC           *)
(* VNeu: A neutral term is a value                                              *)
(* VLam: Abstracting a value yields a value                                     *)
Inductive Value (b v:Type) : Exp b v -> Prop :=
| VNeu : forall (e:Exp b v), Neutral b v e -> Value b v e
| VLam : forall (x:v) (e:Exp b v), Value b v e -> Value b v (Lam x e)

(* NVar: A variable is a neutral term                                           *)
(* NApp: Applying a neutral term to a value yields a neutral term               *)
with Neutral (b v:Type) : Exp b v -> Prop :=
| NVar : forall (x:v), Neutral b v (Var x)
| NApp : forall (e e':Exp b v), 
    Neutral b v e -> Value b v e' -> Neutral b v (App e e')  
.

Arguments Value {b} {v}.
Arguments VNeu {b} {v}.
Arguments VLam {b} {v}.

Arguments Neutral {b} {v}.
Arguments NVar {b} {v}.
Arguments NApp {b} {v}.

Lemma VVar : forall (b v:Type) (x:v), Value (@Var b v x).
Proof. intros b v x. apply VNeu. constructor. Qed.
