Require Import Logic.Prop.Syntax.
Require Import Logic.Prop.Context.
Require Import Logic.Prop.Proof.
Require Import Logic.Prop.Entails.

(* If G :- p has a proof then the semantics entailment G ::- p holds            *)
Lemma Soundness : forall (v:Type) (G:Ctx v) (p:P v) (e: G :- p), G ::- p.
Proof.
  intros v G p e. 
  induction e as 
    [G p|G p q e IH|G p q e IH|G p q e1 IH1 e2 IH2|G p e IH].
  - apply entExtract.
  - apply entWeaken, IH.
  - apply entDeduct, IH.
  - apply entModus with p.
      + apply IH1.
      + apply IH2.
  - apply entReduct, IH.
Qed.

