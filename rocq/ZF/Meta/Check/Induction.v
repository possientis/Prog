Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Exists.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.TypeOf.
Require Import ZF.Meta.Ty.
Require Import ZF.Meta.Unique.

Import ListNotations.

Scheme CheckTInd_  := Induction for CheckT  Sort Prop
  with CheckTsInd_ := Induction for CheckTs Sort Prop
  with CheckPInd_  := Induction for CheckP  Sort Prop.

Combined Scheme Induction_ from CheckTInd_, CheckTsInd_, CheckPInd_.

(* Checked terms, proofs, and argument lists have a joint induction principle.  *)
Proposition Induction :
  forall (E:Env)
    (P:Ctx -> Term -> Ty -> Prop)
    (Q:Ctx -> Terms -> list Ty -> Prop)
    (R:Ctx -> Proof -> Term -> Prop),
    (forall (G:Ctx),
      P G Bot TyProp)                                                   ->
    (forall (G:Ctx),
      P G Top TyProp)                                                   ->
    (forall (G:Ctx) (n:nat) (ty:Ty),
      typeOf G n = Some ty                                              ->
      P G (Var n) ty)                                                   ->
    (forall (G:Ctx) (ty:Ty),
      P G (HoleT ty) ty)                                                ->
    (forall (G:Ctx) (name:Name) (args:Terms) (tys:list Ty) (ty:Ty),
      sigT E name = Some (tys,ty)                                       ->
      CheckTs E G args tys                                              ->
      Q G args tys                                                      ->
      P G (IdentT name args) ty)                                        ->
    (forall (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                ->
      P G x TySet                                                       ->
      CheckT E G y TySet                                                ->
      P G y TySet                                                       ->
      P G (Elem x y) TyProp)                                            ->
    (forall (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                ->
      P G x TySet                                                       ->
      CheckT E G y TySet                                                ->
      P G y TySet                                                       ->
      P G (Leq x y) TyProp)                                             ->
    (forall (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                ->
      P G x TySet                                                       ->
      CheckT E G y TySet                                                ->
      P G y TySet                                                       ->
      P G (Geq x y) TyProp)                                             ->
    (forall (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                ->
      P G x TySet                                                       ->
      CheckT E G y TySet                                                ->
      P G y TySet                                                       ->
      P G (Lt x y) TyProp)                                              ->
    (forall (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                ->
      P G x TySet                                                       ->
      CheckT E G y TySet                                                ->
      P G y TySet                                                       ->
      P G (Gt x y) TyProp)                                              ->
    (forall (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                ->
      P G x TySet                                                       ->
      CheckT E G y TySet                                                ->
      P G y TySet                                                       ->
      P G (Equal x y) TyProp)                                           ->
    (forall (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                ->
      P G x TySet                                                       ->
      CheckT E G y TySet                                                ->
      P G y TySet                                                       ->
      P G (NotEq x y) TyProp)                                           ->
    (forall (G:Ctx) (p q:Term),
      CheckT E G p TyProp                                               ->
      P G p TyProp                                                      ->
      CheckT E G q TyProp                                               ->
      P G q TyProp                                                      ->
      P G (Imp p q) TyProp)                                             ->
    (forall (G:Ctx) (p q:Term),
      CheckT E G p TyProp                                               ->
      P G p TyProp                                                      ->
      CheckT E G q TyProp                                               ->
      P G q TyProp                                                      ->
      P G (Iff p q) TyProp)                                             ->
    (forall (G:Ctx) (p q:Term),
      CheckT E G p TyProp                                               ->
      P G p TyProp                                                      ->
      CheckT E G q TyProp                                               ->
      P G q TyProp                                                      ->
      P G (And p q) TyProp)                                             ->
    (forall (G:Ctx) (p q:Term),
      CheckT E G p TyProp                                               ->
      P G p TyProp                                                      ->
      CheckT E G q TyProp                                               ->
      P G q TyProp                                                      ->
      P G (Or p q) TyProp)                                              ->
    (forall (G:Ctx) (p:Term),
      CheckT E G p TyProp                                               ->
      P G p TyProp                                                      ->
      P G (Not p) TyProp)                                               ->
    (forall (G:Ctx) (p:Term),
      CheckT E (TySet :: G) p TyProp                                    ->
      P (TySet :: G) p TyProp                                           ->
      P G (All p) TyProp)                                               ->
    (forall (G:Ctx) (p:Term),
      CheckT E (TySet :: G) p TyProp                                    ->
      P (TySet :: G) p TyProp                                           ->
      P G (Ex p) TyProp)                                                ->
    (forall (G:Ctx) (p:Term),
      CheckT E (TySet :: G) p TyProp                                    ->
      P (TySet :: G) p TyProp                                           ->
      P G (Lam p) TyClass)                                              ->
    (forall (G:Ctx) (A x:Term),
      CheckT E G A TyClass                                              ->
      P G A TyClass                                                     ->
      CheckT E G x TySet                                                ->
      P G x TySet                                                       ->
      P G (App A x) TyProp)                                             ->
    (forall (G:Ctx) (A:Term) (p q:Proof),
      CheckT E G A TyClass                                              ->
      P G A TyClass                                                     ->
      CheckP E G p (Exists A)                                           ->
      R G p (Exists A)                                                  ->
      CheckP E G q (Unique A)                                           ->
      R G q (Unique A)                                                  ->
      P G (Def A p q) TySet)                                            ->
    (forall (G:Ctx),
      Q G NilT [])                                                      ->
    (forall (G:Ctx) (t:Term) (ts:Terms) (ty:Ty) (tys:list Ty),
      CheckT E G t ty                                                   ->
      P G t ty                                                          ->
      CheckTs E G ts tys                                                ->
      Q G ts tys                                                        ->
      Q G (ConsT t ts) (ty :: tys))                                     ->
    (forall (G:Ctx) (t:Term),
      CheckT E G t TyProp                                               ->
      P G t TyProp                                                      ->
      R G (HoleP t) t)                                                  ->
    (forall (G:Ctx) (t:Term),
      CheckT E G t TyProp                                               ->
      P G t TyProp                                                      ->
      R G (AxiomP t) t)                                                 ->
    (forall (G:Ctx) (name:Name) (args:Terms) (tys:list Ty) (t:Term),
      sigP E name = Some (tys,t)                                        ->
      CheckTs E G args tys                                              ->
      Q G args tys                                                      ->
      R G (IdentP name args) (applyT t args))                           ->
    (forall (G:Ctx) (t:Term) (ty:Ty), CheckT E G t ty -> P G t ty)              /\
    (forall (G:Ctx) (ts:Terms) (tys:list Ty), CheckTs E G ts tys -> Q G ts tys) /\
    (forall (G:Ctx) (p:Proof) (t:Term), CheckP E G p t -> R G p t).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E P Q R H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  intros H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  apply Induction_.
  - intros G. apply H1.
  - intros G. apply H2.
  - intros G n ty G1. apply H3. assumption.
  - intros G ty. apply H4.
  - intros G name args tys ty G1 G2 G3. apply (H5 G name args tys ty); assumption.
  - intros G x y G1 G2 G3 G4. apply H6; assumption.
  - intros G x y G1 G2 G3 G4. apply H7; assumption.
  - intros G x y G1 G2 G3 G4. apply H8; assumption.
  - intros G x y G1 G2 G3 G4. apply H9; assumption.
  - intros G x y G1 G2 G3 G4. apply H10; assumption.
  - intros G x y G1 G2 G3 G4. apply H11; assumption.
  - intros G x y G1 G2 G3 G4. apply H12; assumption.
  - intros G p q G1 G2 G3 G4. apply H13; assumption.
  - intros G p q G1 G2 G3 G4. apply H14; assumption.
  - intros G p q G1 G2 G3 G4. apply H15; assumption.
  - intros G p q G1 G2 G3 G4. apply H16; assumption.
  - intros G p G1 G2. apply H17; assumption.
  - intros G p G1 G2. apply H18; assumption.
  - intros G p G1 G2. apply H19; assumption.
  - intros G p G1 G2. apply H20; assumption.
  - intros G A x G1 G2 G3 G4. apply H21; assumption.
  - intros G A p q G1 G2 G3 G4 G5 G6. apply H22; assumption.
  - intros G. apply H23.
  - intros G t ts ty tys G1 G2 G3 G4. apply H24; assumption.
  - intros G t G1 G2. apply H25; assumption.
  - intros G t G1 G2. apply H26; assumption.
  - intros G name args tys t G1 G2 G3. apply (H27 G name args tys t); assumption.
Qed.
