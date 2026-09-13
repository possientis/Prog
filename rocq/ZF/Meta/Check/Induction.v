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
  forall
    (P:Env -> Ctx -> Term -> Ty -> Prop)
    (Q:Env -> Ctx -> Terms -> list Ty -> Prop)
    (R:Env -> Ctx -> Proof -> Term -> Prop),
    (forall (E:Env) (G:Ctx),
      P E G Bot TyProp)                                                       ->
    (forall (E:Env) (G:Ctx),
      P E G Top TyProp)                                                       ->
    (forall (E:Env) (G:Ctx) (n:nat) (ty:Ty),
      typeOf G n = Some ty                                                    ->
      P E G (Var n) ty)                                                       ->
    (forall (E:Env) (G:Ctx) (ty:Ty),
      P E G (HoleT ty) ty)                                                    ->
    (forall (E:Env) (G:Ctx) (name:Name) (args:Terms) (tys:list Ty) (ty:Ty),
      sigT E name = Some (tys,ty)                                             ->
      CheckTs E G args tys                                                    ->
      Q E G args tys                                                          ->
      P E G (IdentT name args) ty)                                            ->
    (forall (E:Env) (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                      ->
      P E G x TySet                                                           ->
      CheckT E G y TySet                                                      ->
      P E G y TySet                                                           ->
      P E G (Elem x y) TyProp)                                                ->
    (forall (E:Env) (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                      ->
      P E G x TySet                                                           ->
      CheckT E G y TySet                                                      ->
      P E G y TySet                                                           ->
      P E G (Leq x y) TyProp)                                                 ->
    (forall (E:Env) (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                      ->
      P E G x TySet                                                           ->
      CheckT E G y TySet                                                      ->
      P E G y TySet                                                           ->
      P E G (Geq x y) TyProp)                                                 ->
    (forall (E:Env) (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                      ->
      P E G x TySet                                                           ->
      CheckT E G y TySet                                                      ->
      P E G y TySet                                                           ->
      P E G (Lt x y) TyProp)                                                  ->
    (forall (E:Env) (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                      ->
      P E G x TySet                                                           ->
      CheckT E G y TySet                                                      ->
      P E G y TySet                                                           ->
      P E G (Gt x y) TyProp)                                                  ->
    (forall (E:Env) (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                      ->
      P E G x TySet                                                           ->
      CheckT E G y TySet                                                      ->
      P E G y TySet                                                           ->
      P E G (Equal x y) TyProp)                                               ->
    (forall (E:Env) (G:Ctx) (x y:Term),
      CheckT E G x TySet                                                      ->
      P E G x TySet                                                           ->
      CheckT E G y TySet                                                      ->
      P E G y TySet                                                           ->
      P E G (NotEq x y) TyProp)                                               ->
    (forall (E:Env) (G:Ctx) (p q:Term),
      CheckT E G p TyProp                                                     ->
      P E G p TyProp                                                          ->
      CheckT E G q TyProp                                                     ->
      P E G q TyProp                                                          ->
      P E G (Imp p q) TyProp)                                                 ->
    (forall (E:Env) (G:Ctx) (p q:Term),
      CheckT E G p TyProp                                                     ->
      P E G p TyProp                                                          ->
      CheckT E G q TyProp                                                     ->
      P E G q TyProp                                                          ->
      P E G (Iff p q) TyProp)                                                 ->
    (forall (E:Env) (G:Ctx) (p q:Term),
      CheckT E G p TyProp                                                     ->
      P E G p TyProp                                                          ->
      CheckT E G q TyProp                                                     ->
      P E G q TyProp                                                          ->
      P E G (And p q) TyProp)                                                 ->
    (forall (E:Env) (G:Ctx) (p q:Term),
      CheckT E G p TyProp                                                     ->
      P E G p TyProp                                                          ->
      CheckT E G q TyProp                                                     ->
      P E G q TyProp                                                          ->
      P E G (Or p q) TyProp)                                                  ->
    (forall (E:Env) (G:Ctx) (p:Term),
      CheckT E G p TyProp                                                     ->
      P E G p TyProp                                                          ->
      P E G (Not p) TyProp)                                                   ->
    (forall (E:Env) (G:Ctx) (p:Term),
      CheckT E (TySet :: G) p TyProp                                          ->
      P E (TySet :: G) p TyProp                                               ->
      P E G (All p) TyProp)                                                   ->
    (forall (E:Env) (G:Ctx) (p:Term),
      CheckT E (TySet :: G) p TyProp                                          ->
      P E (TySet :: G) p TyProp                                               ->
      P E G (Ex p) TyProp)                                                    ->
    (forall (E:Env) (G:Ctx) (p:Term),
      CheckT E (TySet :: G) p TyProp                                          ->
      P E (TySet :: G) p TyProp                                               ->
      P E G (Lam p) TyClass)                                                  ->
    (forall (E:Env) (G:Ctx) (A x:Term),
      CheckT E G A TyClass                                                    ->
      P E G A TyClass                                                         ->
      CheckT E G x TySet                                                      ->
      P E G x TySet                                                           ->
      P E G (App A x) TyProp)                                                 ->
    (forall (E:Env) (G:Ctx) (A:Term) (p q:Proof),
      CheckT E G A TyClass                                                    ->
      P E G A TyClass                                                         ->
      CheckP E G p (Exists A)                                                 ->
      R E G p (Exists A)                                                      ->
      CheckP E G q (Unique A)                                                 ->
      R E G q (Unique A)                                                      ->
      P E G (Def A p q) TySet)                                                ->
    (forall (E:Env) (G:Ctx),
      Q E G NilT [])                                                          ->
    (forall (E:Env) (G:Ctx) (t:Term) (ts:Terms) (ty:Ty) (tys:list Ty),
      CheckT E G t ty                                                         ->
      P E G t ty                                                              ->
      CheckTs E G ts tys                                                      ->
      Q E G ts tys                                                            ->
      Q E G (ConsT t ts) (ty :: tys))                                         ->
    (forall (E:Env) (G:Ctx) (t:Term),
      CheckT E G t TyProp                                                     ->
      P E G t TyProp                                                          ->
      R E G (HoleP t) t)                                                      ->
    (forall (E:Env) (G:Ctx) (t:Term),
      CheckT E G t TyProp                                                     ->
      P E G t TyProp                                                          ->
      R E G (AxiomP t) t)                                                     ->
    (forall (E:Env) (G:Ctx) (name:Name) (args:Terms) (tys:list Ty) (t:Term),
      sigP E name = Some (tys,t)                                              ->
      CheckTs E G args tys                                                    ->
      Q E G args tys                                                          ->
      R E G (IdentP name args) (applyT t args))                               ->
    (forall (E:Env) (G:Ctx) (t:Term) (ty:Ty),
      CheckT E G t ty -> P E G t ty)                                          /\
    (forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty),
      CheckTs E G ts tys -> Q E G ts tys)                                     /\
    (forall (E:Env) (G:Ctx) (p:Proof) (t:Term),
      CheckP E G p t -> R E G p t).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros P Q R H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  intros H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  assert (forall (E:Env),
    (forall (G:Ctx) (t:Term) (ty:Ty),
      CheckT E G t ty -> P E G t ty)            /\
    (forall (G:Ctx) (ts:Terms) (tys:list Ty),
      CheckTs E G ts tys -> Q E G ts tys)       /\
    (forall (G:Ctx) (p:Proof) (t:Term),
      CheckP E G p t -> R E G p t)) as H28. {
    intros E. apply Induction_.
    - intros G. apply H1.
    - intros G. apply H2.
    - intros G n ty G1. apply H3. assumption.
    - intros G ty. apply H4.
    - intros G name args tys ty G1 G2 G3.
      apply (H5 E G name args tys ty); assumption.
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
    - intros G name args tys t G1 G2 G3.
      apply (H27 E G name args tys t); assumption. }
  split.
  - intros E G t ty H29. apply (H28 E); assumption.
  - split.
    + intros E G ts tys H29. apply (H28 E); assumption.
    + intros E G p t H29. apply (H28 E); assumption.
Qed.
