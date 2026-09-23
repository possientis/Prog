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

Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Set.Incl.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Pair.
Require Import ZF.Meta.Decl.Set.Single.

(* empty : U.                                                                   *)
Definition empty : DeclT :=
  {| paraT := []
  ;  resT  := TySet
  ;  bodyT := FromC (IdentT (Name.qualified "CEM" "empty") (args []))
  |}.

(* toClass empty is equivalent to the empty class.                              *)
Definition ToClass : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "toClass")
            (args [IdentT (Name.local "empty") (args [])])
        ; IdentT (Name.qualified "CEM" "empty") (args [])
        ])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall x, x :< empty <-> False.                                              *)
Definition Charac : DeclP :=
  let concl :=
    All
      (Iff
        (Elem (Var 0) (IdentT (Name.local "empty") (args [])))
        Bot)
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, Incl empty a.                                                      *)
Definition IsIncl : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [IdentT (Name.local "empty") (args []); Var 0])
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall x, not x :< empty.                                                    *)
Definition NoElem : DeclP :=
  let concl :=
    All
      (Not (Elem (Var 0) (IdentT (Name.local "empty") (args []))))
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, a <> empty iff exists x, x :< a.                                   *)
Definition HasElem : DeclP :=
  let concl :=
    Iff
      (NotEq (Var 0) (IdentT (Name.local "empty") (args [])))
      (Ex (Elem (Var 0) (Var 1)))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, a = empty iff not exists x, x :< a.                                *)
Definition HasNoElem : DeclP :=
  let concl :=
    Iff
      (SyntaxT.Equal (Var 0) (IdentT (Name.local "empty") (args [])))
      (Not (Ex (Elem (Var 0) (Var 1))))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, no element belongs to a -> a = empty.                              *)
Definition WhenNoElem : DeclP :=
  let concl :=
    Imp
      (All (Not (Elem (Var 0) (Var 1))))
      (SyntaxT.Equal (Var 0) (IdentT (Name.local "empty") (args [])))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, pair a b <> empty.                                               *)
Definition PairIsNotEmpty : DeclP :=
  let concl :=
    NotEq
      (IdentT (Name.local "pair") (args [Var 1; Var 0]))
      (IdentT (Name.local "empty") (args []))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall x y, ordPair x y <> empty.                                            *)
Definition OrdPairIsNotEmpty : DeclP :=
  let concl :=
    NotEq
      (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))
      (IdentT (Name.local "empty") (args []))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, single a <> empty.                                                 *)
Definition SingletonIsNotEmpty : DeclP :=
  let concl :=
    NotEq
      (IdentT (Name.local "single") (args [Var 0]))
      (IdentT (Name.local "empty") (args []))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, a = empty iff toClass a is the empty class.                        *)
Definition EmptyToClass : DeclP :=
  let concl :=
    Iff
      (SyntaxT.Equal (Var 0) (IdentT (Name.local "empty") (args [])))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "toClass") (args [Var 0])
          ; IdentT (Name.qualified "CEM" "empty") (args [])
          ]))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, a <> empty iff toClass a is not the empty class.                   *)
Definition NotEmptyToClass : DeclP :=
  let concl :=
    Iff
      (NotEq (Var 0) (IdentT (Name.local "empty") (args [])))
      (Not
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "toClass") (args [Var 0])
            ; IdentT (Name.qualified "CEM" "empty") (args [])
            ])))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, Incl a empty -> a = empty.                                         *)
Definition WhenIncl : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl")
        (args [Var 0; IdentT (Name.local "empty") (args [])]))
      (SyntaxT.Equal (Var 0) (IdentT (Name.local "empty") (args [])))
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.qualifyAs "CEM" Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify Pair.exports
  ; Env.unqualify Single.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "empty", empty)
      ]
  ; Env.fromListP
      [ (Name.local "ToClass"           , ToClass)
      ; (Name.local "Charac"            , Charac)
      ; (Name.local "IsIncl"            , IsIncl)
      ; (Name.local "NoElem"            , NoElem)
      ; (Name.local "HasElem"           , HasElem)
      ; (Name.local "HasNoElem"         , HasNoElem)
      ; (Name.local "WhenNoElem"        , WhenNoElem)
      ; (Name.local "PairIsNotEmpty"    , PairIsNotEmpty)
      ; (Name.local "OrdPairIsNotEmpty" , OrdPairIsNotEmpty)
      ; (Name.local "SingletonIsNotEmpty", SingletonIsNotEmpty)
      ; (Name.local "EmptyToClass"      , EmptyToClass)
      ; (Name.local "NotEmptyToClass"   , NotEmptyToClass)
      ; (Name.local "WhenIncl"          , WhenIncl)
      ]
  ].

Definition env : Env := Env.union imports exports.
