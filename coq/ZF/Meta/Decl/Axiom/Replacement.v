Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* forall F, Functional F ->                                                    *)
(* forall a, exists b, forall y, y :< b <-> exists x, x :< a /\ F :(x,y):       *)
Definition Replacement : DeclT :=
  {| paraT := []
  ;  resT  := TyProp
  ;  bodyT :=
      All VarTyClass
        (Imp
          (IdentT "Functional" [Var 0])
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
                        (IdentT "ordPair" [Var 0; Var 1])))))))))
  |}.

Definition imports : Env := Env.unions
  [ Functional.exports
  ; OrdPair.exports
  ].

Definition exports : Env := Env.fromListT
  [ ("Replacement"%string, Replacement)
  ].

Definition env : Env := Env.union imports exports.
