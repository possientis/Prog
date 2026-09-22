Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Set.Pair.
Require Import ZF.Meta.Decl.Set.Single.

(* ordPair a b : U.                                                             *)
Definition ordPair : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TySet
  ;  bodyT :=
      IdentT (Name.local "pair")
        (args [IdentT (Name.local "single") (args [Var 1]);
         IdentT (Name.local "pair") (args [Var 1; Var 0])])
  |}.

(* forall a b x, x :< ordPair a b <-> x = single a \/ x = pair a b.             *)
Definition Charac : DeclP :=
  let concl :=
    All
      (Iff
        (Elem (Var 0)
          (IdentT (Name.local "ordPair") (args [Var 2; Var 1])))
        (Or
          (Equal (Var 0)
            (IdentT (Name.local "single") (args [Var 2])))
          (Equal (Var 0)
            (IdentT (Name.local "pair") (args [Var 2; Var 1])))))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c, single a = pair b c -> a = b /\ a = c.                         *)
Definition ABC : DeclP :=
  let concl :=
    Imp
      (Equal
        (IdentT (Name.local "single") (args [Var 2]))
        (IdentT (Name.local "pair") (args [Var 1; Var 0])))
      (And
        (Equal (Var 2) (Var 1))
        (Equal (Var 2) (Var 0)))
  in
    {| paraP  := [TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c d, ordPair a b = ordPair c d -> a = c /\ b = d.                 *)
Definition Equal : DeclP :=
  let concl :=
    Imp
      (Equal
        (IdentT (Name.local "ordPair") (args [Var 3; Var 2]))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (And
        (Equal (Var 3) (Var 1))
        (Equal (Var 2) (Var 0)))
  in
    {| paraP  := [TySet; TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Pair.exports
  ; Env.unqualify Single.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "ordPair", ordPair)
      ]
  ; Env.fromListP
      [ (Name.local "Charac", Charac)
      ; (Name.local "ABC"   , ABC)
      ; (Name.local "Equal" , Equal)
      ]
  ].

Definition env : Env := Env.union imports exports.
