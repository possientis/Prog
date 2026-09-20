Require Import ZF.Meta.Name.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.Ty.
Require ZF.Meta.InductionT.

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

(* Terms, argument lists, and proofs have a joint induction principle.          *)
Proposition Joint :
  forall (P:Term -> Prop) (Q:Terms -> Prop) (R:Proof -> Prop),
    P Bot                                     ->
    P Top                                     ->
    (forall (n:nat),
      P (Var n))                              ->
    (forall (ty:Ty),
      P (HoleT ty))                           ->
    (forall (name:Name) (args:Terms),
      Q args                                  ->
      P (IdentT name args))                   ->
    (forall (x y:Term),
      P x                                     ->
      P y                                     ->
      P (Elem x y))                           ->
    (forall (x y:Term),
      P x                                     ->
      P y                                     ->
      P (Leq x y))                            ->
    (forall (x y:Term),
      P x                                     ->
      P y                                     ->
      P (Geq x y))                            ->
    (forall (x y:Term),
      P x                                     ->
      P y                                     ->
      P (Lt x y))                             ->
    (forall (x y:Term),
      P x                                     ->
      P y                                     ->
      P (Gt x y))                             ->
    (forall (x y:Term),
      P x                                     ->
      P y                                     ->
      P (Equal x y))                          ->
    (forall (x y:Term),
      P x                                     ->
      P y                                     ->
      P (NotEq x y))                          ->
    (forall (p q:Term),
      P p                                     ->
      P q                                     ->
      P (Imp p q))                            ->
    (forall (p q:Term),
      P p                                     ->
      P q                                     ->
      P (Iff p q))                            ->
    (forall (p q:Term),
      P p                                     ->
      P q                                     ->
      P (And p q))                            ->
    (forall (p q:Term),
      P p                                     ->
      P q                                     ->
      P (Or p q))                             ->
    (forall (p:Term),
      P p                                     ->
      P (Not p))                              ->
    (forall (p:Term),
      P p                                     ->
      P (All p))                              ->
    (forall (p:Term),
      P p                                     ->
      P (Ex p))                               ->
    (forall (p:Term),
      P p                                     ->
      P (Lam p))                              ->
    (forall (A x:Term),
      P A                                     ->
      P x                                     ->
      P (App A x))                            ->
    (forall (A:Term),
      P A                                     ->
      P (Def A))                              ->
    (forall (A:Term),
      P A                                     ->
      P (FromC A))                            ->
    Q NilT                                    ->
    (forall (t:Term) (ts:Terms),
      P t                                     ->
      Q ts                                    ->
      Q (ConsT t ts))                         ->
    (forall (t:Term),
      P t                                     ->
      R (HoleP t))                            ->
    (forall (t:Term),
      P t                                     ->
      R (AxiomP t))                           ->
    (forall (name:Name) (args:Terms),
      Q args                                  ->
      R (IdentP name args))                   ->
    (forall (t:Term), P t)                    /\
    (forall (ts:Terms), Q ts)                 /\
    (forall (p:Proof), R p).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros P Q R H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  intros H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28.
  assert ((forall (t:Term), P t) /\ (forall (ts:Terms), Q ts)) as H29. {
    apply InductionT.Induction; assumption. }
  destruct H29 as [H29 H30].
  split. 1: assumption.
  split. 1: assumption.
  apply (Induction P Q R); assumption.
Qed.
