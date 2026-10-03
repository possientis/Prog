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
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Relation.Compose.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.FunctionOn.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.OneToOne.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Restrict.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.
Require Import ZF.Meta.Decl.Set.Relation.ImageUnderClass.

(* Fun F A B means F is a function from A to B.                                 *)
Definition Fun : DeclT :=
  {| paraT := [TyClass; TyClass; TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      And
        (IdentT (Name.local "FunctionOn") (args [Var 2; Var 1]))
        (IdentT (Name.local "Incl")
          (args [IdentT (Name.local "range") (args [Var 2]); Var 0]))
  |}.

(* forall F G A B C D, Fun respects equivalence in all arguments.               *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 5; Var 4]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 3; Var 1]))
        (Imp
          (IdentT (Name.local "equiv") (args [Var 2; Var 0]))
          (Imp
            (IdentT (Name.local "Fun") (args [Var 5; Var 3; Var 2]))
            (IdentT (Name.local "Fun") (args [Var 4; Var 1; Var 0])))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B, Fun respects equivalence in the function.                    *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Fun") (args [Var 3; Var 1; Var 0]))
        (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, Fun respects equivalence in the domain.                      *)
Definition EquivCompatM : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 0]))
      (Imp
        (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
        (IdentT (Name.local "Fun") (args [Var 3; Var 0; Var 1])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, Fun respects equivalence in the codomain.                    *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
        (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, injectivity on A makes a function from A to B one-to-one.      *)
Definition IsOneToOne : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (Imp
        (All
          (All
            (Imp
              (App (Var 3) (Var 1))
              (Imp
                (App (Var 3) (Var 0))
                (Imp
                  (SyntaxT.Equal
                    (IdentT (Name.local "eval") (args [Var 4; Var 1]))
                    (IdentT (Name.local "eval") (args [Var 4; Var 0])))
                  (SyntaxT.Equal (Var 1) (Var 0)))))))
        (IdentT (Name.local "OneToOne") (args [Var 2])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B G C D, equality is domain equivalence and pointwise equality.   *)
Definition Equal' : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 5; Var 4; Var 3]))
      (Imp
        (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
        (Iff
          (IdentT (Name.local "equiv") (args [Var 5; Var 2]))
          (And
            (IdentT (Name.local "equiv") (args [Var 4; Var 1]))
            (All
              (Imp
                (App (Var 5) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 6; Var 0]))
                  (IdentT (Name.local "eval") (args [Var 3; Var 0]))))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B, pointwise equality on A gives equal functions.               *)
Definition Equal : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 3; Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
        (Imp
          (All
            (Imp
              (App (Var 2) (Var 0))
              (SyntaxT.Equal
                (IdentT (Name.local "eval") (args [Var 4; Var 0]))
                (IdentT (Name.local "eval") (args [Var 3; Var 0])))))
          (IdentT (Name.local "equiv") (args [Var 3; Var 2]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, the image of A is the range for a function from A to B.        *)
Definition ImageOfDomain : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image") (args [Var 2; Var 1])
          ; IdentT (Name.local "range") (args [Var 2])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, images of small classes under a function are small.          *)
Definition ImageIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "image") (args [Var 3; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a function defined on a small class is small.                  *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 1]))
        (IdentT (Name.local "Small") (args [Var 2])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, the inverse image of the range is A.                           *)
Definition InvImageOfRange : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args
                [ IdentT (Name.local "converse") (args [Var 2])
                ; IdentT (Name.local "range") (args [Var 2])
                ])
          ; Var 1
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a function on a small class has small range.                   *)
Definition RangeIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 1]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "range") (args [Var 2])])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, injective functions into small classes have small domains.     *)
Definition DomainIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "OneToOne") (args [Var 2]))
        (Imp
          (IdentT (Name.local "Small") (args [Var 0]))
          (IdentT (Name.local "Small") (args [Var 1]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B C, functions from A to B and B to C compose.                  *)
Definition Compose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 4; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Fun") (args [Var 3; Var 1; Var 0]))
        (IdentT (Name.local "Fun")
          (args [IdentT (Name.local "compose") (args [Var 3; Var 4]); Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B a y, membership is equivalent to evaluation on A.               *)
Definition Eval' : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 4; Var 3; Var 2]))
      (Imp
        (App (Var 3) (Var 1))
        (Iff
          (App (Var 4) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
          (SyntaxT.Equal
            (IdentT (Name.local "eval") (args [Var 4; Var 1]))
            (Var 0))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B a y, membership in a function gives evaluation.                 *)
Definition Eval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 4; Var 3; Var 2]))
      (Imp
        (App (Var 4) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
        (SyntaxT.Equal
          (IdentT (Name.local "eval") (args [Var 4; Var 1]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B a, a function satisfies its graph at F!a.                       *)
Definition Satisfies : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
      (Imp
        (App (Var 2) (Var 0))
        (App (Var 3)
          (IdentT (Name.local "ordPair")
            (args [Var 0; IdentT (Name.local "eval") (args [Var 3; Var 0])]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B a, the value at an element of A lies in B.                      *)
Definition IsInRange : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
      (Imp
        (App (Var 2) (Var 0))
        (App (Var 1) (IdentT (Name.local "eval") (args [Var 3; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C y, image membership is characterized by evaluation on A.      *)
Definition ImageCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
      (All
        (Iff
          (App (IdentT (Name.local "image") (args [Var 4; Var 1])) (Var 0))
          (Ex
            (And
              (App (Var 2) (Var 0))
              (And
                (App (Var 3) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 5; Var 0]))
                  (Var 1)))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B a y, set image membership is characterized by evaluation.       *)
Definition ImageSetCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
      (All
        (Iff
          (Elem
            (Var 0)
            (IdentT (Name.qualified "SIM" "image") (args [Var 4; Var 1])))
          (Ex
            (And
              (Elem (Var 0) (Var 2))
              (And
                (App (Var 3) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 5; Var 0]))
                  (Var 1)))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B C, the domain of the composite is A.                          *)
Definition DomainOfCompose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 4; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Fun") (args [Var 3; Var 1; Var 0]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "domain")
                (args [IdentT (Name.local "compose") (args [Var 3; Var 4])])
            ; Var 2
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B C a, evaluation of a composite of functions.                  *)
Definition ComposeEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 5; Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Fun") (args [Var 4; Var 2; Var 1]))
        (Imp
          (App (Var 3) (Var 0))
          (SyntaxT.Equal
            (IdentT (Name.local "eval")
              (args
                [ IdentT (Name.local "compose") (args [Var 4; Var 5])
                ; Var 0
                ]))
            (IdentT (Name.local "eval")
              (args
                [ Var 4
                ; IdentT (Name.local "eval") (args [Var 5; Var 0])
                ])))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B y, range membership is characterized by evaluation on A.        *)
Definition RangeCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
      (Iff
        (App (IdentT (Name.local "range") (args [Var 3])) (Var 0))
        (Ex
          (And
            (App (Var 3) (Var 0))
            (SyntaxT.Equal
              (IdentT (Name.local "eval") (args [Var 4; Var 0]))
              (Var 1)))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a nonempty domain class gives a nonempty range.                *)
Definition RangeIsNotEmpty : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (Imp
        (Not
          (IdentT (Name.local "equiv")
            (args [Var 1; IdentT (Name.qualified "CEM" "empty") (args [])])))
        (Not
          (IdentT (Name.local "equiv")
            (args
              [ IdentT (Name.local "range") (args [Var 2])
              ; IdentT (Name.qualified "CEM" "empty") (args [])
              ]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a function from A to B equals its restriction to A.            *)
Definition IsRestrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ Var 2
          ; IdentT (Name.local "restrict") (args [Var 2; Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, restricting the domain preserves a function into B.          *)
Definition Restrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 2]))
        (IdentT (Name.local "Fun")
          (args [IdentT (Name.local "restrict") (args [Var 3; Var 0]); Var 0; Var 1])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B G C D E, pointwise agreement gives equal restrictions to E.     *)
Definition RestrictEqual : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Fun") (args [Var 6; Var 5; Var 4]))
      (Imp
        (IdentT (Name.local "Fun") (args [Var 3; Var 2; Var 1]))
        (Imp
          (IdentT (Name.local "Incl") (args [Var 0; Var 5]))
          (Imp
            (IdentT (Name.local "Incl") (args [Var 0; Var 2]))
            (Imp
              (All
                (Imp
                  (App (Var 1) (Var 0))
                  (SyntaxT.Equal
                    (IdentT (Name.local "eval") (args [Var 7; Var 0]))
                    (IdentT (Name.local "eval") (args [Var 4; Var 0])))))
              (IdentT (Name.local "equiv")
                (args
                  [ IdentT (Name.local "restrict") (args [Var 6; Var 0])
                  ; IdentT (Name.local "restrict") (args [Var 3; Var 0])
                  ]))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Compose.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify FunctionOn.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify OneToOne.exports
  ; Env.unqualify Range.exports
  ; Env.unqualify Restrict.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify EvalOfClass.exports
  ; Env.qualifyAs "SIM" ImageUnderClass.exports
  ; Env.qualifyAs "CEM" Class.Empty.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Fun", Fun)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat"             , EquivCompat)
      ; (Name.local "EquivCompatL"            , EquivCompatL)
      ; (Name.local "EquivCompatM"            , EquivCompatM)
      ; (Name.local "EquivCompatR"            , EquivCompatR)
      ; (Name.local "IsOneToOne"              , IsOneToOne)
      ; (Name.local "Equal'"                  , Equal')
      ; (Name.local "Equal"                   , Equal)
      ; (Name.local "ImageOfDomain"           , ImageOfDomain)
      ; (Name.local "ImageIsSmall"            , ImageIsSmall)
      ; (Name.local "IsSmall"                 , IsSmall)
      ; (Name.local "InvImageOfRange"         , InvImageOfRange)
      ; (Name.local "RangeIsSmall"            , RangeIsSmall)
      ; (Name.local "DomainIsSmall"           , DomainIsSmall)
      ; (Name.local "Compose"                 , Compose)
      ; (Name.local "Eval'"                   , Eval')
      ; (Name.local "Eval"                    , Eval)
      ; (Name.local "Satisfies"               , Satisfies)
      ; (Name.local "IsInRange"               , IsInRange)
      ; (Name.local "ImageCharac"             , ImageCharac)
      ; (Name.local "ImageSetCharac"          , ImageSetCharac)
      ; (Name.local "DomainOfCompose"         , DomainOfCompose)
      ; (Name.local "ComposeEval"             , ComposeEval)
      ; (Name.local "RangeCharac"             , RangeCharac)
      ; (Name.local "RangeIsNotEmpty"         , RangeIsNotEmpty)
      ; (Name.local "IsRestrict"              , IsRestrict)
      ; (Name.local "Restrict"                , Restrict)
      ; (Name.local "RestrictEqual"           , RestrictEqual)
      ]
  ].

Definition env : Env := Env.union imports exports.
