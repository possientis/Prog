Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Set.OrdPair.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The ordered pair declaration pairs a singleton with an unordered pair.       *)
Proposition ordPair : CheckT (OrdPair.env) OrdPair.ordPair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
  apply CheckTsCons.
  - apply CheckIdentT with [TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsNil.
  - apply CheckTsCons.
    + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsNil.
    + apply CheckTsNil.
Qed.

(* The characterization proposition is well sorted.                             *)
Proposition Charac : CheckP (OrdPair.env) OrdPair.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (OrdPair.env) (ctxP OrdPair.Charac)
    (conclP OrdPair.Charac) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckIff.
    - apply CheckElem.
      + apply CheckVar. reflexivity.
      + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
    - apply CheckOr.
      + apply CheckEqual.
        * apply CheckVar. reflexivity.
        * apply CheckIdentT with [TySet]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckEqual.
        * apply CheckVar. reflexivity.
        * apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
             ++ apply CheckVar. reflexivity.
             ++ apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Singleton equality with a pair forces equality with both pair members.       *)
Proposition ABC : CheckP (OrdPair.env) OrdPair.ABC.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (OrdPair.env) (ctxP OrdPair.ABC)
    (conclP OrdPair.ABC) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckImp.
    - apply CheckEqual.
      + apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
      + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
    - apply CheckAnd; apply CheckEqual; apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Equality of ordered pairs forces equality of their respective components.    *)
Proposition Equal : CheckP (OrdPair.env) OrdPair.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (OrdPair.env) (ctxP OrdPair.Equal)
    (conclP OrdPair.Equal) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckAll, CheckImp.
    - apply CheckEqual.
      + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
    - apply CheckAnd; apply CheckEqual; apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
