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

Require Import ZF.Meta.Decl.Class.Bounded.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Incl.
Require Import ZF.Meta.Decl.Class.Relation.Domain.
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Class.Relation.Image.
Require Import ZF.Meta.Decl.Class.Small.
Require Import ZF.Meta.Decl.Class.Union2.
Require Import ZF.Meta.Decl.Set.OrdPair.
Require Import ZF.Meta.Decl.Set.Pair.
Require Import ZF.Meta.Decl.Set.Power.
Require Import ZF.Meta.Decl.Set.Single.
Require Import ZF.Meta.Decl.Set.Union2.


(* Relation F <-> forall x, F x -> exists y z, x = :(y,z):.                     *)
Definition Relation : DeclT :=
  {| paraT := [TyClass]
  ;  resT  := TyProp
  ;  bodyT :=
      All
        (Imp
          (App (Var 1) (Var 0))
          (Ex
            (Ex
              (SyntaxT.Equal
                (Var 2)
                (IdentT (Name.local "ordPair") (args [Var 1; Var 0]))))))
  |}.

(* forall F G, equiv F G -> Relation F -> Relation G.                           *)
Definition EquivCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "equiv") (args [Var 1; Var 0]))
      (Imp
        (IdentT (Name.local "Relation") (args [Var 1]))
        (IdentT (Name.local "Relation") (args [Var 0])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F G, Relation F -> Relation G -> Relation (union2 F G).               *)
Definition Union2 : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Relation") (args [Var 1]))
      (Imp
        (IdentT (Name.local "Relation") (args [Var 0]))
        (IdentT (Name.local "Relation")
          (args [IdentT (Name.local "union2") (args [Var 1; Var 0])])))
  in
    {| paraP  := [TyClass; TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall F, Relation F -> Functional F -> Small (domain F) -> Small F.         *)
Definition IsSmall : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Relation") (args [Var 0]))
      (Imp
        (IdentT (Name.local "Functional") (args [Var 0]))
        (Imp
          (IdentT (Name.local "Small")
            (args [IdentT (Name.local "domain") (args [Var 0])]))
          (IdentT (Name.local "Small") (args [Var 0]))))
  in
    {| paraP  := [TyClass]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Bounded.exports
  ; Env.unqualify Equiv.exports
  ; Env.unqualify Class.Incl.exports
  ; Env.unqualify Domain.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify Image.exports
  ; Env.unqualify Small.exports
  ; Env.unqualify Class.Union2.exports
  ; Env.unqualify OrdPair.exports
  ; Env.unqualify Pair.exports
  ; Env.unqualify Power.exports
  ; Env.unqualify Single.exports
  ; Env.qualifyAs "SUN" Decl.Set.Union2.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Relation", Relation)
      ]
  ; Env.fromListP
      [ (Name.local "EquivCompat", EquivCompat)
      ; (Name.local "Union2"     , Union2)
      ; (Name.local "IsSmall"    , IsSmall)
      ]
  ].

Definition env : Env := Env.union imports exports.
