Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Syntax.

Require Import Logic.Fol2.Context.

Fixpoint removeFromScope (v:Type) (e:Eq v) (x:v) (G:Ctx v) : Ctx v :=
  match G with
  | nil               => nil
  | (cons (Var y) G') =>
      match (eqDec x y) with
      | left _        => removeFromScope v e x G'
      | right _       => cons (Var y) (removeFromScope v e x G')
      end
  | (cons (Prp p) G') =>
      match in_dec eqDec x (Fr p) with
      | left _        => removeFromScope v e x G'
      | right _       => cons (Prp p) (removeFromScope v e x G')
    end
 end.

Arguments removeFromScope {v} {e}.

(*
Lemma removeStillValid : forall (v:Type) (e:Eq v) (G:Ctx v) (x:v),
  CtxVal G -> CtxVal (removeFromScope x G).
Proof.
  intros v e G x. induction G as [|ent G' IH]; intro HVal.
  - constructor.
  - destruct ent as [y|p].
    + destruct (eqDec x y) as [HEq|HNeq] eqn:E.
      * subst. simpl. rewrite E. apply IH. apply validInvertV with y,HVal.
      * simpl. rewrite E.

Show.
*)
