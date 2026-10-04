Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Order.Isom.
Require Import ZF.Meta.Decl.Class.Relation.Bij.
Require Import ZF.Meta.Decl.Class.Relation.Bijection.
Require Import ZF.Meta.Decl.Class.Relation.BijectionOn.
Require Import ZF.Meta.Decl.Class.Relation.Compose.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Fun.
Require Import ZF.Meta.Decl.Class.Relation.Function.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.FunctionOn.
Require Import ZF.Meta.Decl.Class.Relation.I.
Require Import ZF.Meta.Decl.Class.Relation.OneToOne.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Relation.
Require Import ZF.Meta.Decl.Class.Relation.Restrict.
Require Import ZF.Meta.Decl.Class.V.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* forall A x, x belongs to I restricted to A iff x is (y,y) for y in A.        *)
Definition Charac : DeclP :=
  let concl :=
    Iff
      (App
          (IdentT (Name.local "restrict")
              (args
                [ IdentT (Name.local "I") (args [])
                ; Var 1
                ]))
          (Var 0))
      (Ex
          (And
              (App
                  (Var 2)
                  (Var 0))
              (SyntaxT.Equal
                  (Var 1)
                  (IdentT (Name.local "ordPair") (args [Var 0; Var 0])))))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A y z, (y,z) belongs to I restricted to A iff y is in A and y=z.      *)
Definition Charac2 : DeclP :=
  let concl :=
    Iff
      (App
          (IdentT (Name.local "restrict")
              (args
                [ IdentT (Name.local "I") (args [])
                ; Var 2
                ]))
          (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (And
          (App
              (Var 2)
              (Var 1))
          (SyntaxT.Equal
              (Var 1)
              (Var 0)))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I restricted to A is functional.                                             *)
Definition IsFunctional : DeclP :=
  let concl :=
    IdentT (Name.local "Functional")
      (args
        [ IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I restricted to A is a relation.                                             *)
Definition IsRelation : DeclP :=
  let concl :=
    IdentT (Name.local "Relation")
      (args
        [ IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I restricted to A is a function.                                             *)
Definition IsFunction : DeclP :=
  let concl :=
    IdentT (Name.local "Function")
      (args
        [ IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* The converse of I restricted to A is I restricted to A.                      *)
Definition Converse : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "converse")
            (args
              [ IdentT (Name.local "restrict")
                  (args
                    [ IdentT (Name.local "I") (args [])
                    ; Var 0
                    ])
              ])
        ; IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I restricted to A is one-to-one.                                             *)
Definition IsOneToOne : DeclP :=
  let concl :=
    IdentT (Name.local "OneToOne")
      (args
        [ IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I restricted to A is a bijection.                                            *)
Definition IsBijection : DeclP :=
  let concl :=
    IdentT (Name.local "Bijection")
      (args
        [ IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* The domain of I restricted to A is A.                                        *)
Definition Domain : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "domain")
            (args
              [ IdentT (Name.local "restrict")
                  (args
                    [ IdentT (Name.local "I") (args [])
                    ; Var 0
                    ])
              ])
        ; Var 0
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* The range of I restricted to A is A.                                         *)
Definition Range : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "range")
            (args
              [ IdentT (Name.local "restrict")
                  (args
                    [ IdentT (Name.local "I") (args [])
                    ; Var 0
                    ])
              ])
        ; Var 0
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I restricted to A is a function on A.                                        *)
Definition IsFunctionOn : DeclP :=
  let concl :=
    IdentT (Name.local "FunctionOn")
      (args
        [ IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ; Var 0
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I restricted to A is a bijection on A.                                       *)
Definition IsBijectionOn : DeclP :=
  let concl :=
    IdentT (Name.local "BijectionOn")
      (args
        [ IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ; Var 0
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* I restricted to A is a bijection from A onto A.                              *)
Definition IsBij : DeclP :=
  let concl :=
    IdentT (Name.local "Bij")
      (args
        [ IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ; Var 0
        ; Var 0
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall A x, if x lies in A then evaluating I restricted to A at x gives x.   *)
Definition Eval : DeclP :=
  let concl :=
    Imp
      (App
          (Var 1)
          (Var 0))
      (SyntaxT.Equal
          (IdentT (Name.local "eval")
              (args
                [ IdentT (Name.local "restrict")
                    (args
                      [ IdentT (Name.local "I") (args [])
                      ; Var 1
                      ])
                ; Var 0
                ]))
          (Var 0))
  in
    {| paraP  := [TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, a function on A that fixes A equals I restricted to A.           *)
Definition Equal : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "FunctionOn") (args [Var 1; Var 0]))
      (Imp
          (All
              (Imp
                  (App
                      (Var 1)
                      (Var 0))
                  (SyntaxT.Equal
                      (IdentT (Name.local "eval") (args [Var 2; Var 0]))
                      (Var 0))))
          (IdentT (Name.local "equiv")
              (args
                [ Var 1
                ; IdentT (Name.local "restrict")
                    (args
                      [ IdentT (Name.local "I") (args [])
                      ; Var 0
                      ])
                ])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall R A, I restricted to A is an isomorphism from R to itself over A.     *)
Definition IsIsom : DeclP :=
  let concl :=
    IdentT (Name.local "Isom")
      (args
        [ IdentT (Name.local "restrict")
            (args
              [ IdentT (Name.local "I") (args [])
              ; Var 0
              ])
        ; Var 1
        ; Var 1
        ; Var 0
        ; Var 0
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, for a bijection F, F inverse after F is I restricted to A.     *)
Definition IsConverseFF : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "compose")
                (args
                  [ IdentT (Name.local "converse") (args [Var 2])
                  ; Var 2
                  ])
            ; IdentT (Name.local "restrict")
                (args
                  [ IdentT (Name.local "I") (args [])
                  ; Var 1
                  ])
            ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, for a bijection F, F after F inverse is I restricted to B.     *)
Definition IsFConverseF : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "compose")
                (args
                  [ Var 2
                  ; IdentT (Name.local "converse") (args [Var 2])
                  ])
            ; IdentT (Name.local "restrict")
                (args
                  [ IdentT (Name.local "I") (args [])
                  ; Var 0
                  ])
            ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, I restricted to B is a left identity for functions A to B.     *)
Definition IdentityL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "compose")
                (args
                  [ IdentT (Name.local "restrict")
                      (args
                        [ IdentT (Name.local "I") (args [])
                        ; Var 0
                        ])
                  ; Var 2
                  ])
            ; Var 2
            ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, I restricted to A is a right identity for functions A to B.    *)
Definition IdentityR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "compose")
                (args
                  [ Var 2
                  ; IdentT (Name.local "restrict")
                      (args
                        [ IdentT (Name.local "I") (args [])
                        ; Var 1
                        ])
                  ])
            ; Var 2
            ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B, equal inverse-left composites force equal bijections.        *)
Definition WhenIsConverseGF : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 1; Var 0]))
      (Imp
          (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
          (Imp
              (IdentT (Name.local "equiv")
                  (args
                    [ IdentT (Name.local "compose")
                        (args
                          [ IdentT (Name.local "converse") (args [Var 2])
                          ; Var 3
                          ])
                    ; IdentT (Name.local "restrict")
                        (args
                          [ IdentT (Name.local "I") (args [])
                          ; Var 1
                          ])
                    ]))
              (IdentT (Name.local "equiv") (args [Var 3; Var 2]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B, equal right-inverse composites force equal bijections.       *)
Definition WhenIsGConverseF : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 1; Var 0]))
      (Imp
          (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
          (Imp
              (IdentT (Name.local "equiv")
                  (args
                    [ IdentT (Name.local "compose")
                        (args
                          [ Var 2
                          ; IdentT (Name.local "converse") (args [Var 3])
                          ])
                    ; IdentT (Name.local "restrict")
                        (args
                          [ IdentT (Name.local "I") (args [])
                          ; Var 0
                          ])
                    ]))
              (IdentT (Name.local "equiv") (args [Var 3; Var 2]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Isom.exports
  ; Env.unqualify Bij.exports
  ; Env.unqualify Bijection.exports
  ; Env.unqualify BijectionOn.exports
  ; Env.unqualify Compose.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Fun.exports
  ; Env.unqualify Function.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify FunctionOn.exports
  ; Env.unqualify I.exports
  ; Env.unqualify OneToOne.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Relation.exports
  ; Env.unqualify Restrict.exports
  ; Env.unqualify V.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify EvalOfClass.exports
  ].

Definition exports : Env := Env.fromListP
  [ (Name.local "Charac"           , Charac)
  ; (Name.local "Charac2"          , Charac2)
  ; (Name.local "IsFunctional"     , IsFunctional)
  ; (Name.local "IsRelation"       , IsRelation)
  ; (Name.local "IsFunction"       , IsFunction)
  ; (Name.local "Converse"         , Converse)
  ; (Name.local "IsOneToOne"       , IsOneToOne)
  ; (Name.local "IsBijection"      , IsBijection)
  ; (Name.local "Domain"           , Domain)
  ; (Name.local "Range"            , Range)
  ; (Name.local "IsFunctionOn"     , IsFunctionOn)
  ; (Name.local "IsBijectionOn"    , IsBijectionOn)
  ; (Name.local "IsBij"            , IsBij)
  ; (Name.local "Eval"             , Eval)
  ; (Name.local "Equal"            , Equal)
  ; (Name.local "IsIsom"           , IsIsom)
  ; (Name.local "IsConverseFF"     , IsConverseFF)
  ; (Name.local "IsFConverseF"     , IsFConverseF)
  ; (Name.local "IdentityL"        , IdentityL)
  ; (Name.local "IdentityR"        , IdentityR)
  ; (Name.local "WhenIsConverseGF" , WhenIsConverseGF)
  ; (Name.local "WhenIsGConverseF" , WhenIsGConverseF)
  ].

Definition env : Env := Env.union imports exports.
