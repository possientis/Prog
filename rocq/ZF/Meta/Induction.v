Require Import ZF.Meta.Name.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Scheme TermInd_  := Induction for Term  Sort Prop
  with ProofInd_ := Induction for Proof Sort Prop
  with TermsInd_ := Induction for Terms Sort Prop.

Combined Scheme Induction_ from TermInd_, ProofInd_, TermsInd_.

(* Terms, proofs, and argument lists have a joint induction principle.          *)
Proposition Induction :
  forall (P:Term -> Prop) (Q:Proof -> Prop) (R:Terms -> Prop),
    P Bot                                     ->
    P Top                                     ->
    (forall (n:nat),
      P (Var n))                              ->
    (forall (ty:Ty),
      P (HoleT ty))                           ->
    (forall (name:Name) (args:Terms),
      R args                                  ->
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
    (forall (A:Term) (p q:Proof),
      P A                                     ->
      Q p                                     ->
      Q q                                     ->
      P (Def A p q))                          ->
    (forall (t:Term),
      P t                                     ->
      Q (HoleP t))                            ->
    (forall (t:Term),
      P t                                     ->
      Q (AxiomP t))                           ->
    (forall (name:Name) (args:Terms),
      R args                                  ->
      Q (IdentP name args))                   ->
    R NilT                                    ->
    (forall (t:Term) (ts:Terms),
      P t                                     ->
      R ts                                    ->
      R (ConsT t ts))                         ->
    (forall (t:Term), P t)                    /\
    (forall (p:Proof), Q p)                   /\
    (forall (ts:Terms), R ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros P Q R H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  intros H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  apply Induction_; try assumption.
  - intros x G1 y G2. apply H6;  assumption.
  - intros x G1 y G2. apply H7;  assumption.
  - intros x G1 y G2. apply H8;  assumption.
  - intros x G1 y G2. apply H9;  assumption.
  - intros x G1 y G2. apply H10; assumption.
  - intros x G1 y G2. apply H11; assumption.
  - intros x G1 y G2. apply H12; assumption.
  - intros x G1 y G2. apply H13; assumption.
  - intros x G1 y G2. apply H14; assumption.
  - intros x G1 y G2. apply H15; assumption.
  - intros x G1 y G2. apply H16; assumption.
  - intros A G1 x G2. apply H21; assumption.
  - intros A G1 p G2 q G3. apply H22; assumption.
  - intros t G1 ts G2. apply H27; assumption.
Qed.
