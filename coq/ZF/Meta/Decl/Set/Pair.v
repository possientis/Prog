Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Declarations.                                                                *)

(* Definition IsPairOf (a b:U) : Class := fun x =>                              *)
(* forall y, y :< x <-> y = a \/ y = b.                                         *)
Definition IsPairOf : DeclT :=
  mkDeclT [TySet; TySet] TyClass
       (Lam
         (All VarTySet
           (Iff
             (Elem (Var 0) (Var 1))
             (Or
               (Equal (Var 0) (Var 3))
               (Equal (Var 0) (Var 2)))))).

(* The existence proof declaration states that some set is a pair of a and b.   *)
Definition pairExists : DeclP :=
  let concl :=
    (Ex VarTySet
      (App
        (IdentT "IsPairOf" [Var 2; Var 1])
        (Var 0)))
  in
    {| paraP := [TySet; TySet]
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* The uniqueness proof declaration states that any two such sets are equal.    *)
Definition pairUnique : DeclP :=
  let concl :=
    (All VarTySet
      (All VarTySet
        (Imp
          (App
            (IdentT "IsPairOf" [Var 3; Var 2])
             (Var 1))
          (Imp
            (App
              (IdentT "IsPairOf" [Var 3; Var 2])
              (Var 0))
            (Equal (Var 1) (Var 0))))))
  in
    {| paraP := [TySet; TySet]
    ; conclP := concl
    ; bodyP  := HoleP concl
    |}.

(* Definition pair (a b:U) : U := Def (IsPairOf a b) exists unique.             *)
Definition pair : DeclT :=
  mkDeclT [TySet; TySet] TySet
       (Def
         (IdentT "IsPairOf" [Var 1; Var 0])
         (IdentP "pairExists" [Var 1; Var 0])
         (IdentP "pairUnique" [Var 1; Var 0])).

(* Environment.                                                                 *)

Definition imports : Env := Env.empty.

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ ("IsPairOf"%string  , IsPairOf)
      ; ("pair"%string      , pair)
      ]
  ; Env.fromListP
      [ ("pairExists"%string, pairExists)
      ; ("pairUnique"%string, pairUnique)
      ]
  ].

Definition env : Env := Env.union imports exports.

(* Body checks.                                                                 *)

(* The declaration body for IsPairOf recognizes the two selected sets.          *)
Proposition IsPairOfCheckBody : CheckDecl Env.empty IsPairOf.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckLam, CheckAll, CheckIff.
  - apply CheckElem; apply CheckVar; reflexivity.
  - apply CheckOr; apply CheckEqual; apply CheckVar; reflexivity.
Qed.

(* The existence proof declaration conclusion is a well-sorted proposition.     *)
Proposition pairExistsCheckConcl :
  CheckT env (ctxP pairExists) (conclP pairExists) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckEx, CheckApp.
  - apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsNil.
  - apply CheckVar. reflexivity.
Qed.

(* The existence proof body is a hole for its stated proposition.               *)
Proposition pairExistsCheckBody :
  CheckP env (ctxP pairExists) (bodyP pairExists) (conclP pairExists).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckHoleP.
  apply pairExistsCheckConcl.
Qed.

(* The uniqueness proof declaration conclusion is a well-sorted proposition.    *)
Proposition pairUniqueCheckConcl :
  CheckT env (ctxP pairUnique) (conclP pairUnique) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckAll, CheckImp.
  - apply CheckApp.
    + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsNil.
    + apply CheckVar. reflexivity.
  - apply CheckImp.
    + apply CheckApp.
      * apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsCons.
           ++ apply CheckVar. reflexivity.
           ++ apply CheckTsNil.
      * apply CheckVar. reflexivity.
    + apply CheckEqual; apply CheckVar; reflexivity.
Qed.

(* The uniqueness proof body is a hole for its stated proposition.              *)
Proposition pairUniqueCheckBody :
  CheckP env (ctxP pairUnique) (bodyP pairUnique) (conclP pairUnique).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckHoleP.
  apply pairUniqueCheckConcl.
Qed.

(* The declaration body for pair denotes a set backed by proof references.      *)
Proposition pairCheckBody : CheckDecl env pair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply (CheckDef _ _ _ (conclP pairExists) (conclP pairUnique)).
  - apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsNil.
  - apply CheckIdentP with [TySet;TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsNil.
  - apply CheckIdentP with [TySet;TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsNil.
Qed.

(* Identifier checks.                                                           *)

(* IsPairOf applied to two set variables is well sorted anywhere.               *)
Proposition IsPairOfCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  Env.sigT e "IsPairOf"%string = Some ([TySet; TySet], TyClass) ->
  typeOf G m = Some TySet ->
  typeOf G n = Some TySet ->
  CheckT e G (IdentT "IsPairOf" [Var m; Var n]) TyClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply CheckIdentT with [TySet;TySet]. 1: assumption.
  - apply CheckTsCons.
    + apply CheckVar. assumption.
    + apply CheckTsCons.
      * apply CheckVar. assumption.
      * apply CheckTsNil.
Qed.

(* Pair applied to two set variables is well sorted anywhere.                   *)
Proposition pairCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  Env.sigT e "pair"%string = Some ([TySet; TySet], TySet) ->
  typeOf G m = Some TySet ->
  typeOf G n = Some TySet ->
  CheckT e G (IdentT "pair" [Var m; Var n]) TySet.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply CheckIdentT with [TySet;TySet]. 1: assumption.
  - apply CheckTsCons.
    + apply CheckVar. assumption.
    + apply CheckTsCons.
      * apply CheckVar. assumption.
      * apply CheckTsNil.
Qed.
