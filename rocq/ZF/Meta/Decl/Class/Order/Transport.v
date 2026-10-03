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

Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Prod.
Require Import ZF.Meta.Decl.Class.Relation.Bij.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

(* transport F R A is the relation R transported along F on A.                  *)
Definition transport : DeclT :=
  {| paraT := [TyClass; TyClass; TyClass]
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (Ex
            (And
              (SyntaxT.Equal
                (Var 2)
                (IdentT (Name.local "ordPair")
                  (args
                    [ IdentT (Name.local "eval") (args [Var 5; Var 1])
                    ; IdentT (Name.local "eval") (args [Var 5; Var 0])
                    ])))
              (And
                (App (Var 3) (Var 1))
                (And
                  (App (Var 3) (Var 0))
                  (App
                    (Var 4)
                    (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))))))))
  |}.

(* forall F R A B y z, transported pairs characterize the source relation.      *)
Definition Charac2F : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 5; Var 3; Var 2]))
      (Imp
        (App (Var 3) (Var 1))
        (Imp
          (App (Var 3) (Var 0))
          (Iff
            (App
              (IdentT (Name.local "transport") (args [Var 5; Var 4; Var 3]))
              (IdentT (Name.local "ordPair")
                (args
                  [ IdentT (Name.local "eval") (args [Var 5; Var 1])
                  ; IdentT (Name.local "eval") (args [Var 5; Var 0])
                  ])))
            (App
              (Var 4)
              (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R A, transported relations are included in F[A] times F[A].         *)
Definition IsIncl : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (IdentT (Name.local "Incl")
          (args [Var 0; IdentT (Name.local "domain") (args [Var 2])]))
        (IdentT (Name.local "Incl")
          (args
            [ IdentT (Name.local "transport") (args [Var 2; Var 1; Var 0])
            ; IdentT (Name.local "prod")
                (args
                  [ IdentT (Name.local "image") (args [Var 2; Var 0])
                  ; IdentT (Name.local "image") (args [Var 2; Var 0])
                  ])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F R A, transport over a small functional domain is small.             *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Functional") (args [Var 2]))
      (Imp
        (IdentT (Name.local "Incl")
          (args [Var 0; IdentT (Name.local "domain") (args [Var 2])]))
        (Imp
          (IdentT (Name.local "Small") (args [Var 0]))
          (IdentT (Name.local "Small")
            (args [IdentT (Name.local "transport") (args [Var 2; Var 1; Var 0])]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Class.Incl.exports
  ; Env.unqualify Prod.exports
  ; Env.unqualify Bij.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify EvalOfClass.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "transport", transport)
      ]
  ; Env.fromListP
      [ (Name.local "Charac2F", Charac2F)
      ; (Name.local "IsIncl"  , IsIncl)
      ; (Name.local "IsSmall" , IsSmall)
      ]
  ].

Definition env : Env := Env.union imports exports.
