Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Exists.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.
Require Import ZF.Meta.Unique.

Import ListNotations.
Open Scope string_scope.

Inductive CheckT (E:Env) : Ctx -> Term -> Ty -> Prop :=
| CheckBot : forall (G:Ctx),
    CheckT E G Bot TyProp
| CheckTop : forall (G:Ctx),
    CheckT E G Top TyProp
| CheckVar : forall (G:Ctx) (n:nat) (ty:Ty),
    typeOf G n = Some ty                     ->
    CheckT E G (Var n) ty
| CheckHoleT : forall (G:Ctx) (ty:Ty),
    CheckT E G (HoleT ty) ty
| CheckIdentT : forall (G:Ctx) (name:Name) (args:Terms)
    (tys:list Ty) (ty:Ty),
    sigT E name = Some (tys,ty)              ->
    CheckTs E G (toList args) tys            ->
    CheckT E G (IdentT name args) ty
| CheckElem : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Elem x y) TyProp
| CheckLeq : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Leq x y) TyProp
| CheckGeq : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Geq x y) TyProp
| CheckLt : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Lt x y) TyProp
| CheckGt : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Gt x y) TyProp
| CheckEqual : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Equal x y) TyProp
| CheckNotEq : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (NotEq x y) TyProp
| CheckImp : forall (G:Ctx) (p q:Term),
    CheckT E G p TyProp                      ->
    CheckT E G q TyProp                      ->
    CheckT E G (Imp p q) TyProp
| CheckIff : forall (G:Ctx) (p q:Term),
    CheckT E G p TyProp                      ->
    CheckT E G q TyProp                      ->
    CheckT E G (Iff p q) TyProp
| CheckAnd : forall (G:Ctx) (p q:Term),
    CheckT E G p TyProp                      ->
    CheckT E G q TyProp                      ->
    CheckT E G (And p q) TyProp
| CheckOr : forall (G:Ctx) (p q:Term),
    CheckT E G p TyProp                      ->
    CheckT E G q TyProp                      ->
    CheckT E G (Or p q) TyProp
| CheckNot : forall (G:Ctx) (p:Term),
    CheckT E G p TyProp                      ->
    CheckT E G (Not p) TyProp
| CheckAll : forall (G:Ctx) (p:Term),
    CheckT E (TySet :: G) p TyProp           ->
    CheckT E G (All p) TyProp
| CheckEx : forall (G:Ctx) (p:Term),
    CheckT E (TySet :: G) p TyProp           ->
    CheckT E G (Ex p) TyProp
| CheckLam : forall (G:Ctx) (p:Term),
    CheckT E (TySet :: G) p TyProp           ->
    CheckT E G (Lam p) TyClass
| CheckApp : forall (G:Ctx) (A x:Term),
    CheckT E G A TyClass                     ->
    CheckT E G x TySet                       ->
    CheckT E G (App A x) TyProp
| CheckDef : forall (G:Ctx) (A:Term) (p q:Proof),
    CheckT E G A TyClass                     ->
    CheckP E G p (Exists A)                  ->
    CheckP E G q (Unique A)                  ->
    CheckT E G (Def A p q) TySet
with CheckTs (E:Env) : Ctx -> list Term -> list Ty -> Prop :=
| CheckTsNil : forall (G:Ctx),
    CheckTs E G [] []
| CheckTsCons : forall (G:Ctx) (t:Term) (ts:list Term) (ty:Ty) (tys:list Ty),
    CheckT E G t ty                          ->
    CheckTs E G ts tys                       ->
    CheckTs E G (t :: ts) (ty :: tys)
with CheckP (E:Env) : Ctx -> Proof -> Term -> Prop :=
| CheckHoleP : forall (G:Ctx) (t:Term),
    CheckT E G t TyProp                      ->
    CheckP E G (HoleP t) t
| CheckAxiomP : forall (G:Ctx) (t:Term),
    CheckT E G t TyProp                      ->
    CheckP E G (AxiomP t) t
| CheckIdentP : forall (G:Ctx) (name:Name) (args:Terms)
    (tys:list Ty) (t:Term),
    sigP E name = Some (tys,t)               ->
    CheckTs E G (toList args) tys            ->
    CheckP E G (IdentP name args) (applyT t args)
.

(* A well-sorted term list has the same length as its sort list.                *)
Proposition CheckTsLength : forall (E:Env) (G:Ctx) (ts:list Term) (tys:list Ty),
  CheckTs E G ts tys                         ->
  List.length ts = List.length tys.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts tys H1.
  induction H1 as [G|G t ts ty tys H1 H2 IH]. 1: reflexivity.
  simpl. rewrite IH. reflexivity.
Qed.

(* The first term in a well-sorted non-empty list has the first sort.           *)
Proposition CheckTsHead :
  forall (E:Env) (G:Ctx) (t:Term) (ts:list Term) (ty:Ty) (tys:list Ty),
    CheckTs E G (t :: ts) (ty :: tys)        ->
    CheckT E G t ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G t ts ty tys H1.
  inversion H1. subst. assumption.
Qed.

(* The tail of a well-sorted non-empty list is well sorted.                     *)
Proposition CheckTsTail :
  forall (E:Env) (G:Ctx) (t:Term) (ts:list Term) (ty:Ty) (tys:list Ty),
    CheckTs E G (t :: ts) (ty :: tys)        ->
    CheckTs E G ts tys.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G t ts ty tys H1.
  inversion H1. subst. assumption.
Qed.

(* Appending well-sorted term lists preserves matching sorts.                   *)
Proposition CheckTsApp :
  forall (E:Env) (G:Ctx) (ts us:list Term) (tys uys:list Ty),
    CheckTs E G ts tys                       ->
    CheckTs E G us uys                       ->
    CheckTs E G (ts ++ us) (tys ++ uys).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts us tys uys H1.
  generalize dependent uys.
  generalize dependent us.
  (* The proof follows the checked prefix; the empty prefix adds nothing.       *)
  induction H1 as [G|G t ts ty tys H1 H2 IH]; intros us uys H3. 1: assumption.
  (* Matching heads remain matching heads after appending the same suffixes.    *)
  apply CheckTsCons. assumption. apply IH. assumption.
Qed.

(* Reversing a well-sorted term list preserves matching sorts.                  *)
Proposition CheckTsRev :
  forall (E:Env) (G:Ctx) (ts:list Term) (tys:list Ty),
    CheckTs E G ts tys                       ->
    CheckTs E G (rev ts) (rev tys).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts tys H1.
  (* The empty checked list remains empty after reversal.                       *)
  induction H1 as [G|G t ts ty tys H1 H2 IH]. 1: apply CheckTsNil.
  (* Reversal moves the checked head to the end of the checked reversed tail.   *)
  assert (rev (t :: ts)   = List.app (rev ts) [t])   as H3. { reflexivity. }
  assert (rev (ty :: tys) = List.app (rev tys) [ty]) as H4. { reflexivity. }
  rewrite H3, H4. apply CheckTsApp. 1: assumption.
  apply CheckTsCons. 1: assumption. apply CheckTsNil.
Qed.

(* Matching entries in a well-sorted term list have matching sorts.             *)
Proposition CheckTsNth :
  forall (E:Env) (G:Ctx) (ts:list Term) (tys:list Ty) (n:nat) (t:Term) (ty:Ty),
    CheckTs E G ts tys                       ->
    nth_error ts n  = Some t                 ->
    nth_error tys n = Some ty                ->
    CheckT E G t ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts tys n t ty H1.
  generalize dependent ty.
  generalize dependent t.
  generalize dependent n.
  induction H1 as [G|G t' ts ty' tys H1 H2 IH]; intros n t ty H3 H4.
  - destruct n as [|n]; discriminate.
  - destruct n as [|n].
    + inversion H3. subst. inversion H4. subst. assumption.
    + apply IH with n; assumption.
Qed.

(* Matching entries in a well-sorted term list have matching context sorts.     *)
Proposition CheckTsTypeOf :
  forall (E:Env) (G:Ctx) (ts:list Term) (D:Ctx) (n:nat) (t:Term) (ty:Ty),
    CheckTs E G ts D                         ->
    nth_error ts n = Some t                  ->
    typeOf D n = Some ty                     ->
    CheckT E G t ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G ts D n t ty H1 H2 H3.
  (* The type context lookup is the same as the matching list lookup.           *)
  rewrite TypeOfNthError in H3.
  (* The structural list theorem then gives the sort of the selected term.      *)
  apply (CheckTsNth E G ts D n); assumption.
Qed.

(* A selected checked argument has the sort found in the reversed signature.    *)
Proposition CheckArgT :
  forall (E:Env) (G:Ctx) (args:Terms) (tys:list Ty) (n:nat) (ty:Ty),
    CheckTs E G (toList args) tys            ->
    typeOf (rev tys) n = Some ty             ->
    CheckT E G (argT args n) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G args tys n ty H1 H2.
  unfold argT.
  (* If the reversed argument lookup succeeds, reversal and context lookup match
     it with the corresponding sort.                                            *)
  destruct (nthT (revT args) n) as [t|] eqn:H3.
  - unfold nthT in H3.
    apply (CheckTsTypeOf E G (toList (revT args)) (rev tys) n); try assumption.
    assert (toList (revT args) = rev (toList args)) as H4. {
      unfold revT. apply ToListFromList.
    }
    rewrite H4. apply CheckTsRev. assumption.
    (* If the reversed argument lookup failed, the matching reversed sort lookup
       would fail too, contradicting the successful context lookup.             *)
  -  unfold nthT in H3.
    assert (toList (revT args) = rev (toList args)) as H4. {
      unfold revT. apply ToListFromList.
    }
    assert (List.length (toList (revT args)) = List.length (rev tys)) as H5. {
      rewrite H4, length_rev, length_rev. apply CheckTsLength with E G. assumption.
    }
    assert (nth_error (rev tys) n = None) as H6. {
      apply nth_error_None. rewrite <- H5. apply nth_error_None. assumption.
    }
    rewrite TypeOfNthError in H2.
    rewrite H2 in H6. discriminate.
Qed.

