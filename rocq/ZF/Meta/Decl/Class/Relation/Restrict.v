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

Require Import ZF.Meta.Decl.Axiom.Classic.
Require Import ZF.Meta.Decl.Class.Diff.
Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Relation.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* restrict F A x <-> exists y z, x = :(y,z): /\ A y /\ F :(y,z):.              *)
Definition restrict : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (Ex
            (And
              (SyntaxT.Equal
                (Var 2)
                (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
              (And
                (App (Var 3) (Var 1))
                (App (Var 4)
                  (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))))))
  |}.

(* forall F A y z, restrict F A :(y,z): <-> A y /\ F :(y,z):.                   *)
Definition Charac2 : DeclP :=
  let concl :=
    Iff
      (App
        (IdentT (Name.local "restrict") (args [Var 3; Var 2]))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (And
        (App (Var 2) (Var 1))
        (App (Var 3) (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B, F ~ G -> A ~ B -> restrict F A ~ restrict G B.               *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "restrict") (args [Var 3; Var 1])
            ; IdentT (Name.local "restrict") (args [Var 2; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A, F ~ G -> restrict F A ~ restrict G A.                          *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "restrict") (args [Var 2; Var 0])
          ; IdentT (Name.local "restrict") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, A ~ B -> restrict F A ~ restrict F B.                          *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "restrict") (args [Var 2; Var 1])
          ; IdentT (Name.local "restrict") (args [Var 2; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, Relation (restrict F A).                                         *)
Definition IsRelation : DeclP :=
  let concl :=
    IdentT (Name.local "Relation")
      (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, Functional F -> Functional (restrict F A).                       *)
Definition IsFunctional : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (IdentT (Name.local "Functional")
        (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, domain (restrict F A) ~ inter2 A (domain F).                     *)
Definition DomainOf : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "domain")
            (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])])
        ; IdentT (Name.local "inter2")
            (args [Var 0; IdentT (Name.local "domain") (args [Var 1])])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, range (restrict F A) ~ image F A.                                *)
Definition RangeOf : DeclP :=
  let concl :=
    IdentT (Name.local "equiv")
      (args
        [ IdentT (Name.local "range")
            (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])])
        ; IdentT (Name.local "image") (args [Var 1; Var 0])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, Incl (range (restrict F A)) (range F).                           *)
Definition RangeIsIncl : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args
        [ IdentT (Name.local "range")
            (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])])
        ; IdentT (Name.local "range") (args [Var 1])
        ])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, Functional F -> Small A -> Small (restrict F A).                 *)
Definition IsSmallR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, Incl (restrict F A) F.                                           *)
Definition IsIncl : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [IdentT (Name.local "restrict") (args [Var 1; Var 0]); Var 1])
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, Small F -> Small (restrict F A).                                 *)
Definition IsSmallL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Small") (args [Var 1]))
      (IdentT (Name.local "Small")
        (args [IdentT (Name.local "restrict") (args [Var 1; Var 0])]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Relation F <-> F ~ restrict F (domain F).                          *)
Definition RelationCharac : DeclP :=
  let concl :=
    Iff
      (IdentT (Name.local "Relation") (args [Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ Var 0
          ; IdentT (Name.local "restrict")
              (args [Var 0; IdentT (Name.local "domain") (args [Var 0])])
          ]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, A <= B -> restrict (restrict F B) A ~ restrict F A.            *)
Definition TowerProperty : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "restrict")
              (args [IdentT (Name.local "restrict") (args [Var 2; Var 0]); Var 1])
          ; IdentT (Name.local "restrict") (args [Var 2; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, small range cover makes A small.                               *)
Definition LesserThanRangeIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (Imp
          (IdentT (Name.local "Incl")
            (args
              [ Var 1
              ; IdentT (Name.local "range")
                  (args [IdentT (Name.local "restrict") (args [Var 2; Var 0])])
              ]))
          (IdentT (Name.local "Small") (args [Var 1]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A x, Functional F -> A x -> eval (restrict F A) x = eval F x.       *)
Definition Eval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (App (Var 1) (Var 0))
        (SyntaxT.Equal
          (IdentT (Name.local "eval")
            (args
              [ IdentT (Name.local "restrict") (args [Var 2; Var 1])
              ; Var 0
              ]))
          (IdentT (Name.local "eval") (args [Var 2; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, Functional F -> bounded range cover implies Small A.             *)
Definition LesserThanRangeOfRestrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 1]))
      (Imp
        (Ex
          (IdentT (Name.local "equiv")
            (args
              [ IdentT (Name.local "diff")
                  (args
                    [ Var 1
                    ; IdentT (Name.local "range")
                        (args
                          [ IdentT (Name.local "restrict")
                              (args
                                [ Var 2
                                ; IdentT (Name.local "toClass") (args [Var 0])
                                ])
                          ])
                    ])
              ; IdentT (Name.local "empty") (args [])
              ])))
        (IdentT (Name.local "Small") (args [Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, A ~ empty -> restrict F A ~ empty.                               *)
Definition WhenZero : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv")
        (args [Var 0; IdentT (Name.local "empty") (args [])]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "restrict") (args [Var 1; Var 0])
          ; IdentT (Name.local "empty") (args [])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Classic.exports
  ; Env.unqualify Diff.exports
  ; Env.unqualify Class.Empty.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Relation.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify EvalOfClass.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "restrict", restrict)
      ]
  ; Env.fromListP
      [ (Name.local "Charac2"                  , Charac2)
      ; (Name.local "EquivCompat"              , EquivCompat)
      ; (Name.local "EquivCompatL"             , EquivCompatL)
      ; (Name.local "EquivCompatR"             , EquivCompatR)
      ; (Name.local "IsRelation"               , IsRelation)
      ; (Name.local "IsFunctional"             , IsFunctional)
      ; (Name.local "DomainOf"                 , DomainOf)
      ; (Name.local "RangeOf"                  , RangeOf)
      ; (Name.local "RangeIsIncl"              , RangeIsIncl)
      ; (Name.local "IsSmallR"                 , IsSmallR)
      ; (Name.local "IsIncl"                   , IsIncl)
      ; (Name.local "IsSmallL"                 , IsSmallL)
      ; (Name.local "RelationCharac"           , RelationCharac)
      ; (Name.local "TowerProperty"            , TowerProperty)
      ; (Name.local "LesserThanRangeIsSmall"   , LesserThanRangeIsSmall)
      ; (Name.local "Eval"                     , Eval)
      ; (Name.local "LesserThanRangeOfRestrict", LesserThanRangeOfRestrict)
      ; (Name.local "WhenZero"                 , WhenZero)
      ]
  ].

Definition env : Env := Env.union imports exports.
