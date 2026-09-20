Require Import ZF.Meta.Name.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.SyntaxT.

(* Proofs are induced using already-known facts about terms and arguments.      *)
Proposition Induction :
  forall (P:Term -> Prop) (Q:Terms -> Prop) (R:Proof -> Prop),
    (forall (t:Term), P t)                    ->
    (forall (ts:Terms), Q ts)                 ->
    (forall (t:Term),
      P t                                     ->
      R (HoleP t))                            ->
    (forall (t:Term),
      P t                                     ->
      R (AxiomP t))                           ->
    (forall (name:Name) (args:Terms),
      Q args                                  ->
      R (IdentP name args))                   ->
    forall (p:Proof), R p.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros P Q R H1 H2 H3 H4 H5 p.
  destruct p as [t|t|name args].
  - apply H3. apply H1.
  - apply H4. apply H1.
  - apply H5. apply H2.
Qed.
