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
Require Import ZF.Meta.Decl.Class.Relation.BijectionOn.
Require Import ZF.Meta.Decl.Class.Relation.Compose.
Require Import ZF.Meta.Decl.Class.Relation.Converse.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Fun.
Require Import ZF.Meta.Decl.Class.Relation.FunctionOn.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Relation.Inj.
Require Import ZF.Meta.Decl.Class.Relation.OneToOne.
Require Import ZF.Meta.Decl.Class.Relation.Onto.
Require Import ZF.Meta.Decl.Class.Relation.Range.
Require Import ZF.Meta.Decl.Class.Relation.Restrict.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.
Require Import ZF.Meta.Decl.Set.Relation.ImageUnderClass.

(* Bij F A B means F is a bijection from A to B.                                *)
Definition Bij : DeclT :=
  {| paraT := [TyClass; TyClass; TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      And
        (IdentT (Name.local "BijectionOn") (args [Var 2; Var 1]))
        (IdentT (Name.local "equiv")
          (args [IdentT (Name.local "range") (args [Var 2]); Var 0]))
  |}.

(* forall F G A B C D, Bij respects equivalence in all arguments.               *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 5; Var 4]))
      (Imp
        (IdentT (Name.local "equiv") (args [Var 3; Var 1]))
        (Imp
          (IdentT (Name.local "equiv") (args [Var 2; Var 0]))
          (Imp
            (IdentT (Name.local "Bij") (args [Var 5; Var 3; Var 2]))
            (IdentT (Name.local "Bij") (args [Var 4; Var 1; Var 0])))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B, Bij respects equivalence in the function.                    *)
Definition EquivCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 3; Var 1; Var 0]))
        (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, Bij respects equivalence in the domain.                      *)
Definition EquivCompatM : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 2; Var 0]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
        (IdentT (Name.local "Bij") (args [Var 3; Var 0; Var 1])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, Bij respects equivalence in the codomain.                    *)
Definition EquivCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
        (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a bijection from A to B is a function from A to B.             *)
Definition IsFun : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "Fun") (args [Var 2; Var 1; Var 0]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a bijection from A to B is one-to-one.                         *)
Definition IsOneToOne : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "OneToOne") (args [Var 2]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a bijection from A to B is defined on A.                       *)
Definition IsFunctionOn : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "FunctionOn") (args [Var 2; Var 1]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a bijection from A to B is an injection from A to B.           *)
Definition IsInj : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "Inj") (args [Var 2; Var 1; Var 0]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a bijection from A to B is a surjection from A to B.           *)
Definition IsOnto : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "Onto") (args [Var 2; Var 1; Var 0]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B G C D, equality is domain equivalence and pointwise equality.   *)
Definition Equal' : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 5; Var 4; Var 3]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
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

(* forall F G A B, pointwise equality on A gives equal bijections.              *)
Definition Equal : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
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

(* forall F A B, the image of A is B for a bijection.                           *)
Definition ImageOfDomain : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args [IdentT (Name.local "image") (args [Var 2; Var 1]); Var 0]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, images of small classes under a bijection are small.         *)
Definition ImageIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args [IdentT (Name.local "image") (args [Var 3; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a bijection defined on a small class is small.                 *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 1]))
        (IdentT (Name.local "Small") (args [Var 2])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, the inverse image of B is A for a bijection.                   *)
Definition InvImageOfRange : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args [IdentT (Name.local "converse") (args [Var 2]); Var 0])
          ; Var 1
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a bijection from a small class has small codomain.             *)
Definition RangeIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 1]))
        (IdentT (Name.local "Small") (args [Var 0])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a bijection into a small class has small domain.               *)
Definition DomainIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small") (args [Var 1])))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G A B C, bijections from A to B and B to C compose.                 *)
Definition Compose : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 4; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 3; Var 1; Var 0]))
        (IdentT (Name.local "Bij")
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
      (IdentT (Name.local "Bij") (args [Var 4; Var 3; Var 2]))
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

(* forall F A B a y, membership in a bijection gives evaluation.                *)
Definition Eval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 4; Var 3; Var 2]))
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

(* forall F A B a, a bijection satisfies its graph at F!a.                      *)
Definition Satisfies : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
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
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
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
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
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
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
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
      (IdentT (Name.local "Bij") (args [Var 4; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 3; Var 1; Var 0]))
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

(* forall F G A B C a, evaluation of a composite of bijections.                 *)
Definition ComposeEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 5; Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 4; Var 2; Var 1]))
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

(* forall F A B y, codomain membership is characterized by evaluation on A.     *)
Definition RangeCharac : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Iff
        (App (Var 1) (Var 0))
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

(* forall F A B C, the image of a subclass of A is included in B.               *)
Definition ImageIncl : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 2]))
        (IdentT (Name.local "Incl")
          (args [IdentT (Name.local "image") (args [Var 3; Var 0]); Var 1])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a nonempty domain class gives a nonempty codomain.             *)
Definition RangeIsNotEmpty : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (Imp
        (Not
          (IdentT (Name.local "equiv")
            (args [Var 1; IdentT (Name.qualified "CEM" "empty") (args [])])))
        (Not
          (IdentT (Name.local "equiv")
            (args [Var 0; IdentT (Name.qualified "CEM" "empty") (args [])]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, a bijection from A to B equals its restriction to A.           *)
Definition IsRestrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
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

(* forall F A B C, restricting to C gives a bijection onto F image C.           *)
Definition Restrict : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 2]))
        (IdentT (Name.local "Bij")
          (args
            [ IdentT (Name.local "restrict") (args [Var 3; Var 0])
            ; Var 0
            ; IdentT (Name.local "image") (args [Var 3; Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B G C D E, pointwise agreement gives equal restrictions to E.     *)
Definition RestrictEqual : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 6; Var 5; Var 4]))
      (Imp
        (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
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

(* forall F A B C, inverse images under bijections are small.                   *)
Definition InvImageIsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Small") (args [Var 0]))
        (IdentT (Name.local "Small")
          (args
            [ IdentT (Name.local "image")
                (args [IdentT (Name.local "converse") (args [Var 3]); Var 0])
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B, the converse is a bijection from B to A.                       *)
Definition Converse : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 2; Var 1; Var 0]))
      (IdentT (Name.local "Bij")
        (args [IdentT (Name.local "converse") (args [Var 2]); Var 0; Var 1]))
  in
    {| paraP  := [TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B y, converse evaluation at an element of B lies in A.            *)
Definition ConverseEvalIsInDomain : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Imp
        (App (Var 1) (Var 0))
        (App
          (Var 2)
          (IdentT (Name.local "eval")
            (args [IdentT (Name.local "converse") (args [Var 3]); Var 0]))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B x, applying the converse to F!x returns x on A.                 *)
Definition ConverseEvalOfEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Imp
        (App (Var 2) (Var 0))
        (SyntaxT.Equal
          (IdentT (Name.local "eval")
            (args
              [ IdentT (Name.local "converse") (args [Var 3])
              ; IdentT (Name.local "eval") (args [Var 3; Var 0])
              ]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B y, applying F to the converse value returns y on B.             *)
Definition EvalOfConverseEval : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Imp
        (App (Var 1) (Var 0))
        (SyntaxT.Equal
          (IdentT (Name.local "eval")
            (args
              [ Var 3
              ; IdentT (Name.local "eval")
                  (args [IdentT (Name.local "converse") (args [Var 3]); Var 0])
              ]))
          (Var 0)))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, the inverse image of the image is C inside A.                *)
Definition InvImageOfImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 2]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "image")
                (args
                  [ IdentT (Name.local "converse") (args [Var 3])
                  ; IdentT (Name.local "image") (args [Var 3; Var 0])
                  ])
            ; Var 0
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C, the image of the inverse image is C inside B.                *)
Definition ImageOfInvImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 3; Var 2; Var 1]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
        (IdentT (Name.local "equiv")
          (args
            [ IdentT (Name.local "image")
                (args
                  [ Var 3
                  ; IdentT (Name.local "image")
                      (args [IdentT (Name.local "converse") (args [Var 3]); Var 0])
                  ])
            ; Var 0
            ])))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B x y, bijection evaluation is injective on A.                    *)
Definition EvalInjective : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 4; Var 3; Var 2]))
      (Imp
        (App (Var 3) (Var 1))
        (Imp
          (App (Var 3) (Var 0))
          (Imp
            (SyntaxT.Equal
              (IdentT (Name.local "eval") (args [Var 4; Var 1]))
              (IdentT (Name.local "eval") (args [Var 4; Var 0])))
            (SyntaxT.Equal (Var 1) (Var 0)))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C a, F!a lies in F[C] iff a lies in C.                          *)
Definition EvalInImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 4; Var 3; Var 2]))
      (Imp
        (App (Var 3) (Var 0))
        (Iff
          (App
            (IdentT (Name.local "image") (args [Var 4; Var 1]))
            (IdentT (Name.local "eval") (args [Var 4; Var 0])))
          (App (Var 1) (Var 0))))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C D, bijections preserve binary intersections by image.         *)
Definition Inter2Image : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 4; Var 3; Var 2]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args [Var 4; IdentT (Name.local "inter2") (args [Var 1; Var 0])])
          ; IdentT (Name.local "inter2")
              (args
                [ IdentT (Name.local "image") (args [Var 4; Var 1])
                ; IdentT (Name.local "image") (args [Var 4; Var 0])
                ])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F A B C D, bijections preserve class differences by image.            *)
Definition DiffImage : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Bij") (args [Var 4; Var 3; Var 2]))
      (IdentT (Name.local "equiv")
        (args
          [ IdentT (Name.local "image")
              (args [Var 4; IdentT (Name.local "diff") (args [Var 1; Var 0])])
          ; IdentT (Name.local "diff")
              (args
                [ IdentT (Name.local "image") (args [Var 4; Var 1])
                ; IdentT (Name.local "image") (args [Var 4; Var 0])
                ])
          ]))
  in
    {| paraP  := [TyClass; TyClass; TyClass; TyClass; TyClass]
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
  ; Env.unqualify BijectionOn.exports
  ; Env.unqualify Compose.exports
  ; Env.unqualify Converse.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Fun.exports
  ; Env.unqualify FunctionOn.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Inj.exports
  ; Env.unqualify OneToOne.exports
  ; Env.unqualify Onto.exports
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
      [ (Name.local "Bij", Bij)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat"                 , EquivCompat)
      ; (Name.local "EquivCompatL"                , EquivCompatL)
      ; (Name.local "EquivCompatM"                , EquivCompatM)
      ; (Name.local "EquivCompatR"                , EquivCompatR)
      ; (Name.local "IsFun"                       , IsFun)
      ; (Name.local "IsOneToOne"                  , IsOneToOne)
      ; (Name.local "IsFunctionOn"                , IsFunctionOn)
      ; (Name.local "IsInj"                       , IsInj)
      ; (Name.local "IsOnto"                      , IsOnto)
      ; (Name.local "Equal'"                      , Equal')
      ; (Name.local "Equal"                       , Equal)
      ; (Name.local "ImageOfDomain"               , ImageOfDomain)
      ; (Name.local "ImageIsSmall"                , ImageIsSmall)
      ; (Name.local "IsSmall"                     , IsSmall)
      ; (Name.local "InvImageOfRange"             , InvImageOfRange)
      ; (Name.local "RangeIsSmall"                , RangeIsSmall)
      ; (Name.local "DomainIsSmall"               , DomainIsSmall)
      ; (Name.local "Compose"                     , Compose)
      ; (Name.local "Eval'"                       , Eval')
      ; (Name.local "Eval"                        , Eval)
      ; (Name.local "Satisfies"                   , Satisfies)
      ; (Name.local "IsInRange"                   , IsInRange)
      ; (Name.local "ImageCharac"                 , ImageCharac)
      ; (Name.local "ImageSetCharac"              , ImageSetCharac)
      ; (Name.local "DomainOfCompose"             , DomainOfCompose)
      ; (Name.local "ComposeEval"                 , ComposeEval)
      ; (Name.local "RangeCharac"                 , RangeCharac)
      ; (Name.local "ImageIncl"                   , ImageIncl)
      ; (Name.local "RangeIsNotEmpty"             , RangeIsNotEmpty)
      ; (Name.local "IsRestrict"                  , IsRestrict)
      ; (Name.local "Restrict"                    , Restrict)
      ; (Name.local "RestrictEqual"               , RestrictEqual)
      ; (Name.local "InvImageIsSmall"             , InvImageIsSmall)
      ; (Name.local "Converse"                    , Converse)
      ; (Name.local "ConverseEvalIsInDomain"      , ConverseEvalIsInDomain)
      ; (Name.local "ConverseEvalOfEval"          , ConverseEvalOfEval)
      ; (Name.local "EvalOfConverseEval"          , EvalOfConverseEval)
      ; (Name.local "InvImageOfImage"             , InvImageOfImage)
      ; (Name.local "ImageOfInvImage"             , ImageOfInvImage)
      ; (Name.local "EvalInjective"               , EvalInjective)
      ; (Name.local "EvalInImage"                 , EvalInImage)
      ; (Name.local "Inter2Image"                 , Inter2Image)
      ; (Name.local "DiffImage"                   , DiffImage)
      ]
  ].

Definition env : Env := Env.union imports exports.
