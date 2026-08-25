Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Sig.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition sig : Sig := fun name =>
  if String.eqb name "Functional" then Some ([TyClass]      , TyProp) else
  if String.eqb name "ordPair"    then Some ([TySet; TySet], TySet ) else
  None.

(* forall F, Functional F ->                                                    *)
(* forall a, exists b, forall y, y :< b <-> exists x, x :< a /\ F :(x,y):       *)
Definition Replacement : Term :=
  All VarTyClass
    (Imp
      (Ident "Functional" [Var 0])
      (All VarTySet
        (Ex VarTySet
          (All VarTySet
            (Iff
              (Elem (Var 0) (Var 1))
              (Ex VarTySet
                (And
                  (Elem (Var 0) (Var 3))
                  (App
                    (Var 4)
                    (Ident "ordPair" [Var 0; Var 1]))))))))).

(* The replacement example is a proposition in the local test signature.        *)
Proposition HasTy : HasTy sig Ctx.empty Replacement TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyImp.
  - apply HasTyIdent with (argTys := [TyClass]). 1: reflexivity.
    apply HasTysCons.
    + apply (HasTyVar _ _ _ TyClass). reflexivity.
    + apply HasTysNil.
  - apply HasTyAll, HasTyEx, HasTyAll, HasTyIff.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyEx, HasTyAnd.
      * apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
      * apply HasTyApp.
        -- apply (HasTyVar _ _ _ TyClass). reflexivity.
        -- apply HasTyIdent with (argTys := [TySet; TySet]). 1: reflexivity.
           apply HasTysCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTysCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTysNil.
Qed.
