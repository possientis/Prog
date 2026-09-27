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

Require Import ZF.Meta.Decl.Axiom.Extensionality.
Require Import ZF.Meta.Decl.Class.Equiv.
Require Import ZF.Meta.Decl.Class.Union2.
Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Incl.
Require Import ZF.Meta.Decl.Set.Pair.
Require Import ZF.Meta.Decl.Set.Single.

(* union2 a b : U.                                                              *)
Definition union2 : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TySet
  ;  bodyT :=
      FromC
        (IdentT (Name.qualified "CUN" "union2")
          (args
            [ IdentT (Name.local "toClass") (args [Var 1])
            ; IdentT (Name.local "toClass") (args [Var 0])
            ]))
  |}.

(* forall a b x, x :< union2 a b <-> x :< a \/ x :< b.                          *)
Definition Charac : DeclP :=
  let concl :=
    All
      (Iff
        (Elem (Var 0) (IdentT (Name.local "union2") (args [Var 2; Var 1])))
        (Or
          (Elem (Var 0) (Var 2))
          (Elem (Var 0) (Var 1))))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, union2 a b = union2 b a.                                         *)
Definition Comm : DeclP :=
  let concl :=
    SyntaxT.Equal
      (IdentT (Name.local "union2") (args [Var 1; Var 0]))
      (IdentT (Name.local "union2") (args [Var 0; Var 1]))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c, union2 (union2 a b) c = union2 a (union2 b c).                 *)
Definition Assoc : DeclP :=
  let concl :=
    SyntaxT.Equal
      (IdentT (Name.local "union2")
        (args
          [ IdentT (Name.local "union2") (args [Var 2; Var 1])
          ; Var 0
          ]))
      (IdentT (Name.local "union2")
        (args
          [ Var 2
          ; IdentT (Name.local "union2") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c d, Incl a b -> Incl c d -> Incl (union2 a c) (union2 b d).      *)
Definition InclCompat : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 3; Var 2]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl")
          (args
            [ IdentT (Name.local "union2") (args [Var 3; Var 1])
            ; IdentT (Name.local "union2") (args [Var 2; Var 0])
            ])))
  in
    {| paraP  := [TySet; TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c, Incl a b -> Incl (union2 a c) (union2 b c).                    *)
Definition InclCompatL : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "union2") (args [Var 2; Var 0])
          ; IdentT (Name.local "union2") (args [Var 1; Var 0])
          ]))
  in
    {| paraP  := [TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c, Incl a b -> Incl (union2 c a) (union2 c b).                    *)
Definition InclCompatR : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 1]))
      (IdentT (Name.local "Incl")
        (args
          [ IdentT (Name.local "union2") (args [Var 0; Var 2])
          ; IdentT (Name.local "union2") (args [Var 0; Var 1])
          ]))
  in
    {| paraP  := [TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, b = union2 a b <-> Incl a b.                                     *)
Definition WhenEqualR : DeclP :=
  let concl :=
    Iff
      (SyntaxT.Equal
        (Var 0)
        (IdentT (Name.local "union2") (args [Var 1; Var 0])))
      (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, a = union2 a b <-> Incl b a.                                     *)
Definition WhenEqualL : DeclP :=
  let concl :=
    Iff
      (SyntaxT.Equal
        (Var 1)
        (IdentT (Name.local "union2") (args [Var 1; Var 0])))
      (IdentT (Name.local "Incl") (args [Var 0; Var 1]))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, Incl a (union2 a b).                                             *)
Definition IsInclL : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [Var 1; IdentT (Name.local "union2") (args [Var 1; Var 0])])
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, Incl b (union2 a b).                                             *)
Definition IsInclR : DeclP :=
  let concl :=
    IdentT (Name.local "Incl")
      (args [Var 0; IdentT (Name.local "union2") (args [Var 1; Var 0])])
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b, pair a b = union2 (single a) (single b).                         *)
Definition PairAsUnion2 : DeclP :=
  let concl :=
    SyntaxT.Equal
      (IdentT (Name.local "pair") (args [Var 1; Var 0]))
      (IdentT (Name.local "union2")
        (args
          [ IdentT (Name.local "single") (args [Var 1])
          ; IdentT (Name.local "single") (args [Var 0])
          ]))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, union2 empty a = a.                                                *)
Definition IdentityL : DeclP :=
  let concl :=
    SyntaxT.Equal
      (IdentT (Name.local "union2")
        (args [IdentT (Name.local "empty") (args []); Var 0]))
      (Var 0)
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a, union2 a empty = a.                                                *)
Definition IdentityR : DeclP :=
  let concl :=
    SyntaxT.Equal
      (IdentT (Name.local "union2")
        (args [Var 0; IdentT (Name.local "empty") (args [])]))
      (Var 0)
  in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c, Incl a c -> Incl b c -> Incl (union2 a b) c.                   *)
Definition IsIncl : DeclP :=
  let concl :=
    Imp
      (IdentT (Name.local "Incl") (args [Var 2; Var 0]))
      (Imp
        (IdentT (Name.local "Incl") (args [Var 1; Var 0]))
        (IdentT (Name.local "Incl")
          (args [IdentT (Name.local "union2") (args [Var 2; Var 1]); Var 0])))
  in
    {| paraP  := [TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* forall a b c x, x :< union2 a (union2 b c) <-> x :< a \/ x :< b \/ x :< c.   *)
Definition Charac3 : DeclP :=
  let concl :=
    Iff
      (Elem
        (Var 0)
        (IdentT (Name.local "union2")
          (args
            [ Var 3
            ; IdentT (Name.local "union2") (args [Var 2; Var 1])
            ])))
      (Or
        (Elem (Var 0) (Var 3))
        (Or (Elem (Var 0) (Var 2)) (Elem (Var 0) (Var 1))))
  in
    {| paraP  := [TySet; TySet; TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Extensionality.exports
  ; Env.unqualify Equiv.exports
  ; Env.qualifyAs "CUN" Union2.exports
  ; Env.unqualify Empty.exports
  ; Env.unqualify Incl.exports
  ; Env.unqualify Pair.exports
  ; Env.unqualify Single.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "union2", union2)
      ]
  ; Env.fromListP
      [ (Name.local "Charac"       , Charac)
      ; (Name.local "Comm"         , Comm)
      ; (Name.local "Assoc"        , Assoc)
      ; (Name.local "InclCompat"   , InclCompat)
      ; (Name.local "InclCompatL"  , InclCompatL)
      ; (Name.local "InclCompatR"  , InclCompatR)
      ; (Name.local "WhenEqualR"   , WhenEqualR)
      ; (Name.local "WhenEqualL"   , WhenEqualL)
      ; (Name.local "IsInclL"      , IsInclL)
      ; (Name.local "IsInclR"      , IsInclR)
      ; (Name.local "PairAsUnion2" , PairAsUnion2)
      ; (Name.local "IdentityL"    , IdentityL)
      ; (Name.local "IdentityR"    , IdentityR)
      ; (Name.local "IsIncl"       , IsIncl)
      ; (Name.local "Charac3"      , Charac3)
      ]
  ].

Definition env : Env := Env.union imports exports.
