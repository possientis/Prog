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

Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Prod.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Relation.
Require Import ZF.Meta.Decl.Class.Relation.Switch.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Class.V.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* converse F x <-> exists y z, x = :(z,y): /\ F :(y,z):.                       *)
Definition converse : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (Ex
            (And
              (SyntaxT.Equal
                (Var 2)
                (IdentT (Name.local "ordPair") (args [Var 0; Var 1])))
              (App
                (Var 3)
                (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))))))
  |}.

(* forall F y z, converse F :(y,z): -> F :(z,y):.                               *)
Definition Charac2 : DeclP :=
  let concl :=
    Imp
      (App
        (IdentT (Name.local "converse") (args [Var 2]))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (App
        (Var 2)
        (IdentT (Name.local "ordPair") (args [Var 0; Var 1])))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F y z, F :(z,y): -> converse F :(y,z):.                               *)
Definition Charac2Rev : DeclP :=
  let concl :=
    Imp
      (App
        (Var 2)
        (IdentT (Name.local "ordPair") (args [Var 0; Var 1])))
      (App
        (IdentT (Name.local "converse") (args [Var 2]))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, equiv F G -> equiv (converse F) (converse G).                    *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "converse") (args [Var 1])
          ; IdentT (Name.local "converse") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, Incl F G -> Incl (converse F) (converse G).                      *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "converse") (args [Var 1])
          ; IdentT (Name.local "converse") (args [Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, equiv (converse F) (image Switch F).                               *)
Definition ImageUnderSwitch : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "converse") (args [Var 0])
        ; IdentT (Name.local "image")
            (args [IdentT (Name.local "Switch") (args []); Var 0])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Small F -> Small (converse F).                                     *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 0]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "converse") (args [Var 0])]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Relation (converse F).                                             *)
Definition IsRelation : DeclP :=
  let concl :=
    IdentT (Name.local "Relation")
      (args [IdentT (Name.local "converse") (args [Var 0])])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Incl (converse (converse F)) F.                                    *)
Definition IsIncl : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "converse")
            (args [IdentT (Name.local "converse") (args [Var 0])])
        ; Var 0
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Relation F <-> equiv (converse (converse F)) F.                    *)
Definition IsIdempotent : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Relation") (args [Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "converse")
              (args [IdentT (Name.local "converse") (args [Var 0])])
          ; Var 0
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, equiv (converse F) (converse (inter2 F (prod V V))).               *)
Definition IsConverseOfOrderedPairs : DeclP :=
  let square :=
    IdentT (Name.local "prod")
      (args [IdentT (Name.local "V") (args []); IdentT (Name.local "V") (args [])])
  in
  let pairs := IdentT (Name.local "inter2") (args [Var 0; square]) in
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "converse") (args [Var 0])
        ; IdentT (Name.local "converse") (args [pairs])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, equiv (domain (converse F)) (range F).                             *)
Definition Domain : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "domain")
            (args [IdentT (Name.local "converse") (args [Var 0])])
        ; IdentT (Name.local "range") (args [Var 0])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, equiv (range (converse F)) (domain F).                             *)
Definition Range : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "range")
            (args [IdentT (Name.local "converse") (args [Var 0])])
        ; IdentT (Name.local "domain") (args [Var 0])
        ])
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F x y z, Functional (converse F) -> F :(x,z): -> F :(y,z): -> x = y.  *)
Definition WhenFunctional : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional")
        (args [IdentT (Name.local "converse") (args [Var 3])]))
      (Imp
        (App
          (Var 3)
          (IdentT (Name.local "ordPair") (args [Var 2; Var 0])))
        (Imp
          (App
            (Var 3)
            (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
          (SyntaxT.Equal (Var 2) (Var 1))))
  in
    {| paraP  := [TyClass; TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, Functional (converse F) -> equiv F[A /\ B] (F[A] /\ F[B]).     *)
Definition Inter2Image : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional")
        (args [IdentT (Name.local "converse") (args [Var 2])]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args
                [ Var 2
                ; IdentT (Name.local "inter2") (args [Var 1; Var 0])
                ])
          ; IdentT (Name.local "inter2")
              (args
                [ IdentT (Name.local "image") (args [Var 2; Var 1])
                ; IdentT (Name.local "image") (args [Var 2; Var 0])
                ])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Prod.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Relation.exports
  ; Env.unqualify Switch.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify V.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "converse", converse)
      ]
  ; Env.fromListP
      [ (Name.local "Charac2"                 , Charac2)
      ; (Name.local "Charac2Rev"              , Charac2Rev)
      ; (Name.local "EquivCompat"             , EquivCompat)
      ; (Name.local "InclCompat"              , InclCompat)
      ; (Name.local "ImageUnderSwitch"        , ImageUnderSwitch)
      ; (Name.local "IsSmall"                 , IsSmall)
      ; (Name.local "IsRelation"              , IsRelation)
      ; (Name.local "IsIncl"                  , IsIncl)
      ; (Name.local "IsIdempotent"            , IsIdempotent)
      ; (Name.local "IsConverseOfOrderedPairs", IsConverseOfOrderedPairs)
      ; (Name.local "Domain"                  , Domain)
      ; (Name.local "Range"                   , Range)
      ; (Name.local "WhenFunctional"          , WhenFunctional)
      ; (Name.local "Inter2Image"             , Inter2Image)
      ]
  ].

Definition env : Env := Env.union imports exports.
