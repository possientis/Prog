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

Require Import ZF.Meta.Decl.Class.Diff.
Require Import ZF.Meta.Decl.Class.Empty.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Inter2.
Require Import ZF.Meta.Decl.Class.Relation.Bijection.
Require Import ZF.Meta.Decl.Class.Relation.Compose.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Function.
Require Import ZF.Meta.Decl.Class.Relation.FunctionOn.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Restrict.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.
Require Import ZF.Meta.Decl.Set.Relation.ImageUnderClass.

(* BijectionOn F A means F is a bijection with domain A.                        *)
Definition BijectionOn : DeclT :=
  {| paraT := [TyClass; TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      And
        (IdentT (Name.local "Bijection") (args [Var 1]))
        (IdentT (Name.local "equiv")
          (args [IdentT (Name.local "domain") (args [Var 1]); Var 0]))
  |}.

(* forall F G A B, BijectionOn respects equivalence in both arguments.          *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
        (Imp
          (IdentT (Name.local "BijectionOn") (args [Var 3; Var 1]))
          (IdentT (Name.local "BijectionOn") (args [Var 2; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A, BijectionOn respects equivalence in the function.              *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "BijectionOn") (args [Var 2; Var 0]))
        (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, BijectionOn respects equivalence in the domain.                *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
        (IdentT (Name.local "BijectionOn") (args [Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, a bijection on A is a function on A.                             *)
Definition IsFunctionOn : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0]))
      (IdentT (Name.local "FunctionOn") (args [Var 1; Var 0]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B, equality is domain equivalence and pointwise equality.       *)
Definition Equal' : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 3; Var 1]))
      (Imp
        (IdentT (Name.local "BijectionOn") (args [Var 2; Var 0]))
        (Iff
          (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
          (And
            (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
            (All
              (Imp
                (App (Var 2) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 4; Var 0]))
                  (IdentT (Name.local "eval") (args [Var 3; Var 0]))))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A, pointwise equality on A gives equal bijections.                *)
Definition Equal : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 0]))
      (Imp
        (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0]))
        (Imp
          (All
            (Imp
              (App (Var 1) (Var 0))
              (SyntaxT.Equal
                (IdentT (Name.local "eval") (args [Var 3; Var 0]))
                (IdentT (Name.local "eval") (args [Var 2; Var 0])))))
          (IdentT (Name.local "equiv") (args [Var 2; Var 1]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, the image of A is the range for a bijection on A.                *)
Definition ImageOfDomain : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image") (args [Var 1; Var 0])
          ; IdentT (Name.local "range") (args [Var 1])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, images of small classes under a bijection on A are small.      *)
Definition ImageIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "image") (args [Var 2; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, a bijection defined on a small class is small.                   *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small") (args [Var 1])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, the inverse image of the range is A.                             *)
Definition InvImageOfRange : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args
                [ IdentT (Name.local "converse") (args [Var 1])
                ; IdentT (Name.local "range") (args [Var 1])
                ])
          ; Var 0
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, a bijection on a small class has small range.                    *)
Definition RangeIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "range") (args [Var 1])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, a bijection on A with small range has small domain.              *)
Definition DomainIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "range") (args [Var 1])]))
        (IdentT (Name.local "Small") (args [Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B, compatible bijections on classes compose on A.               *)
Definition Compose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 3; Var 1]))
      (Imp
        (IdentT (Name.local "BijectionOn") (args [Var 2; Var 0]))
        (Imp
          (IdentT (Name.local "Incl")
            (args [IdentT (Name.local "range") (args [Var 3]); Var 0]))
          (IdentT (Name.local "BijectionOn")
            (args [IdentT (Name.local "compose") (args [Var 2; Var 3]); Var 1]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A a y, membership is equivalent to evaluation on A.                 *)
Definition Eval' : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 3; Var 2]))
      (Imp
        (App (Var 2) (Var 1))
        (Iff
          (App (Var 3) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
          (SyntaxT.Equal
            (IdentT (Name.local "eval") (args [Var 3; Var 1]))
            (Var 0))))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A a y, membership in a bijection on A gives evaluation.             *)
Definition Eval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 3; Var 2]))
      (Imp
        (App (Var 3) (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
        (SyntaxT.Equal
          (IdentT (Name.local "eval") (args [Var 3; Var 1]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A a, a bijection on A satisfies its graph at F!a.                   *)
Definition Satisfies : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (App (Var 1) (Var 0))
        (App (Var 2)
          (IdentT (Name.local "ordPair")
            (args [Var 0; IdentT (Name.local "eval") (args [Var 2; Var 0])]))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A a, the value at an element of A lies in the range.                *)
Definition IsInRange : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (App (Var 1) (Var 0))
        (App
          (IdentT (Name.local "range") (args [Var 2]))
          (IdentT (Name.local "eval") (args [Var 2; Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B y, image membership is characterized by evaluation on A.        *)
Definition ImageCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (All
        (Iff
          (App (IdentT (Name.local "image") (args [Var 3; Var 1])) (Var 0))
          (Ex
            (And
              (App (Var 2) (Var 0))
              (And
                (App (Var 3) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 4; Var 0]))
                  (Var 1)))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A a y, set image membership is characterized by evaluation.         *)
Definition ImageSetCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (All
        (Iff
          (Elem
            (Var 0)
            (IdentT (Name.qualified "SIM" "image") (args [Var 3; Var 1])))
          (Ex
            (And
              (Elem (Var 0) (Var 2))
              (And
                (App (Var 3) (Var 0))
                (SyntaxT.Equal
                  (IdentT (Name.local "eval") (args [Var 4; Var 0]))
                  (Var 1)))))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B a, composite domain is A with F!a in B.                       *)
Definition DomainOfCompose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 4; Var 2]))
      (Imp
        (IdentT (Name.local "BijectionOn") (args [Var 3; Var 1]))
        (Iff
          (App
            (IdentT (Name.local "domain")
              (args [IdentT (Name.local "compose") (args [Var 3; Var 4])]))
            (Var 0))
          (And
            (App (Var 2) (Var 0))
            (App (Var 1) (IdentT (Name.local "eval") (args [Var 4; Var 0]))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B a, evaluation of a composite of bijections on classes.        *)
Definition ComposeEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 4; Var 2]))
      (Imp
        (IdentT (Name.local "BijectionOn") (args [Var 3; Var 1]))
        (Imp
          (App (Var 2) (Var 0))
          (Imp
            (App (Var 1) (IdentT (Name.local "eval") (args [Var 4; Var 0])))
            (SyntaxT.Equal
              (IdentT (Name.local "eval")
                (args
                  [ IdentT (Name.local "compose") (args [Var 3; Var 4])
                  ; Var 0
                  ]))
              (IdentT (Name.local "eval")
                (args
                  [ Var 3
                  ; IdentT (Name.local "eval") (args [Var 4; Var 0])
                  ]))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A y, range membership is characterized by evaluation on A.          *)
Definition RangeCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Iff
        (App (IdentT (Name.local "range") (args [Var 2])) (Var 0))
        (Ex
          (And
            (App (Var 2) (Var 0))
            (SyntaxT.Equal
              (IdentT (Name.local "eval") (args [Var 3; Var 0]))
              (Var 1)))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, a nonempty domain class gives a nonempty range.                  *)
Definition RangeIsNotEmpty : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0]))
      (Imp
        (Not
          (IdentT (Name.local "equiv")
            (args [Var 0; IdentT (Name.qualified "CEM" "empty") (args [])])))
        (Not
          (IdentT (Name.local "equiv")
            (args
              [ IdentT (Name.local "range") (args [Var 1])
              ; IdentT (Name.qualified "CEM" "empty") (args [])
              ]))))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A, a bijection on A equals its restriction to A.                    *)
Definition IsRestrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ Var 1
          ; IdentT (Name.local "restrict") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, restricting a bijection on A to B gives a bijection on B.      *)
Definition Restrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
        (IdentT (Name.local "BijectionOn")
          (args [IdentT (Name.local "restrict") (args [Var 2; Var 0]); Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B C, pointwise agreement gives equal restrictions to C.         *)
Definition RestrictEqual : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 4; Var 2]))
      (Imp
        (IdentT (Name.local "BijectionOn") (args [Var 3; Var 1]))
        (Imp
          (IdentT (Name.local "Incl") (args [Var 0; Var 2]))
          (Imp
            (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
            (Imp
              (All
                (Imp
                  (App (Var 1) (Var 0))
                  (SyntaxT.Equal
                    (IdentT (Name.local "eval") (args [Var 5; Var 0]))
                    (IdentT (Name.local "eval") (args [Var 4; Var 0])))))
              (IdentT (Name.local "equiv")
                (args
                  [ IdentT (Name.local "restrict") (args [Var 4; Var 0])
                  ; IdentT (Name.local "restrict") (args [Var 3; Var 0])
                  ]))))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, inverse images under bijections on A are small.                *)
Definition InvImageIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args
            [ IdentT (Name.local "image")
                (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, the converse is a bijection on the range class.                *)
Definition Converse : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "equiv")
          (args [IdentT (Name.local "range") (args [Var 2]); Var 0]))
        (IdentT (Name.local "BijectionOn")
          (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A b, converse evaluation at a range element lies in A.              *)
Definition ConverseEvalIsInDomain : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (App (IdentT (Name.local "range") (args [Var 2])) (Var 0))
        (App
          (Var 1)
          (IdentT (Name.local "eval")
            (args [IdentT (Name.local "converse") (args [Var 2]); Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A x, applying the converse to F!x returns x on A.                   *)
Definition ConverseEvalOfEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (App (Var 1) (Var 0))
        (SyntaxT.Equal
          (IdentT (Name.local "eval")
            (args
              [ IdentT (Name.local "converse") (args [Var 2])
              ; IdentT (Name.local "eval") (args [Var 2; Var 0])
              ]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A y, applying F to the converse value returns y on the range.       *)
Definition EvalOfConverseEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (App (IdentT (Name.local "range") (args [Var 2])) (Var 0))
        (SyntaxT.Equal
          (IdentT (Name.local "eval")
            (args
              [ Var 2
              ; IdentT (Name.local "eval")
                  (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
              ]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, the inverse image of the image is B inside A.                  *)
Definition InvImageOfImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "image")
                (args
                  [ IdentT (Name.local "converse") (args [Var 2])
                  ; IdentT (Name.local "image") (args [Var 2; Var 0])
                  ])
            ; Var 0
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, the image of the inverse image is B on the range.              *)
Definition ImageOfInvImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl")
          (args [Var 0; IdentT (Name.local "range") (args [Var 2])]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "image")
                (args
                  [ Var 2
                  ; IdentT (Name.local "image")
                      (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
                  ])
            ; Var 0
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A x y, bijection-on evaluation is injective on A.                   *)
Definition EvalInjective : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 3; Var 2]))
      (Imp
        (App (Var 2) (Var 1))
        (Imp
          (App (Var 2) (Var 0))
          (Imp
            (SyntaxT.Equal
              (IdentT (Name.local "eval") (args [Var 3; Var 1]))
              (IdentT (Name.local "eval") (args [Var 3; Var 0])))
            (SyntaxT.Equal (Var 1) (Var 0)))))
  in
    {| paraP  := [TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B a, F!a lies in F[B] iff a lies in B.                            *)
Definition EvalInImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 3; Var 2]))
      (Imp
        (App (Var 2) (Var 0))
        (Iff
          (App
            (IdentT (Name.local "image") (args [Var 3; Var 1]))
            (IdentT (Name.local "eval") (args [Var 3; Var 0])))
          (App (Var 1) (Var 0))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, every bijection is a bijection on its domain.                      *)
Definition BijectionIsBijectionOn : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bijection") (args [Var 0]))
      (IdentT (Name.local "BijectionOn")
        (args [Var 0; IdentT (Name.local "domain") (args [Var 0])]))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, bijections on A preserve binary intersections by image.      *)
Definition Inter2Image : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 3; Var 2]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args [Var 3; IdentT (Name.local "inter2") (args [Var 1; Var 0])])
          ; IdentT (Name.local "inter2")
              (args
                [ IdentT (Name.local "image") (args [Var 3; Var 1])
                ; IdentT (Name.local "image") (args [Var 3; Var 0])
                ])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, bijections on A preserve class differences by image.         *)
Definition DiffImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "BijectionOn") (args [Var 3; Var 2]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args [Var 3; IdentT (Name.local "diff") (args [Var 1; Var 0])])
          ; IdentT (Name.local "diff")
              (args
                [ IdentT (Name.local "image") (args [Var 3; Var 1])
                ; IdentT (Name.local "image") (args [Var 3; Var 0])
                ])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Diff.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Inter2.exports
  ; Env.unqualify Bijection.exports
  ; Env.unqualify Compose.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Function.exports
  ; Env.unqualify FunctionOn.exports
  ; Env.unqualify Image.exports
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
      [ (Name.local "BijectionOn", BijectionOn)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat"               , EquivCompat)
      ; (Name.local "EquivCompatL"              , EquivCompatL)
      ; (Name.local "EquivCompatR"              , EquivCompatR)
      ; (Name.local "IsFunctionOn"              , IsFunctionOn)
      ; (Name.local "Equal'"                    , Equal')
      ; (Name.local "Equal"                     , Equal)
      ; (Name.local "ImageOfDomain"             , ImageOfDomain)
      ; (Name.local "ImageIsSmall"              , ImageIsSmall)
      ; (Name.local "IsSmall"                   , IsSmall)
      ; (Name.local "InvImageOfRange"           , InvImageOfRange)
      ; (Name.local "RangeIsSmall"              , RangeIsSmall)
      ; (Name.local "DomainIsSmall"             , DomainIsSmall)
      ; (Name.local "Compose"                   , Compose)
      ; (Name.local "Eval'"                     , Eval')
      ; (Name.local "Eval"                      , Eval)
      ; (Name.local "Satisfies"                 , Satisfies)
      ; (Name.local "IsInRange"                 , IsInRange)
      ; (Name.local "ImageCharac"               , ImageCharac)
      ; (Name.local "ImageSetCharac"            , ImageSetCharac)
      ; (Name.local "DomainOfCompose"           , DomainOfCompose)
      ; (Name.local "ComposeEval"               , ComposeEval)
      ; (Name.local "RangeCharac"               , RangeCharac)
      ; (Name.local "RangeIsNotEmpty"           , RangeIsNotEmpty)
      ; (Name.local "IsRestrict"                , IsRestrict)
      ; (Name.local "Restrict"                  , Restrict)
      ; (Name.local "RestrictEqual"             , RestrictEqual)
      ; (Name.local "InvImageIsSmall"           , InvImageIsSmall)
      ; (Name.local "Converse"                  , Converse)
      ; (Name.local "ConverseEvalIsInDomain"    , ConverseEvalIsInDomain)
      ; (Name.local "ConverseEvalOfEval"        , ConverseEvalOfEval)
      ; (Name.local "EvalOfConverseEval"        , EvalOfConverseEval)
      ; (Name.local "InvImageOfImage"           , InvImageOfImage)
      ; (Name.local "ImageOfInvImage"           , ImageOfInvImage)
      ; (Name.local "EvalInjective"             , EvalInjective)
      ; (Name.local "EvalInImage"               , EvalInImage)
      ; (Name.local "BijectionIsBijectionOn"    , BijectionIsBijectionOn)
      ; (Name.local "Inter2Image"               , Inter2Image)
      ; (Name.local "DiffImage"                 , DiffImage)
      ]
  ].

Definition env : Env := Env.union imports exports.
