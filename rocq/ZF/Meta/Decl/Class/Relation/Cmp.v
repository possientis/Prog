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
Require Import ZF.Meta.Decl.Class.Relation.Functional.
Require Import ZF.Meta.Decl.Set.OrdPair.

(* Cmp is the class of pairs (((x,y),(y',z)),(x,z)).                            *)
Definition Cmp : DeclT :=
  {| paraT := []
  ;  resT  := TyClass
  ;  bodyT :=
      Lam
        (Ex
          (Ex
            (Ex
              (Ex
                (SyntaxT.Equal
                  (Var 4)
                  (IdentT (Name.local "ordPair")
                    (args
                      [ IdentT (Name.local "ordPair")
                          (args
                            [ IdentT (Name.local "ordPair") (args [Var 3; Var 2])
                            ; IdentT (Name.local "ordPair") (args [Var 1; Var 0])
                            ])
                      ; IdentT (Name.local "ordPair") (args [Var 3; Var 0])
                      ])))))))
  |}.

(* forall u v, Cmp (u,v) iff u and v have the comparison shape.                 *)
Definition Charac2 : DeclP :=
  let concl :=
    Iff
      (App
        (IdentT (Name.local "Cmp") (args []))
        (IdentT (Name.local "ordPair") (args [Var 1; Var 0])))
      (Ex
        (Ex
          (Ex
            (Ex
              (And
                (SyntaxT.Equal
                  (Var 5)
                  (IdentT (Name.local "ordPair")
                    (args
                      [ IdentT (Name.local "ordPair") (args [Var 3; Var 2])
                      ; IdentT (Name.local "ordPair") (args [Var 1; Var 0])
                      ])))
                (SyntaxT.Equal
                  (Var 4)
                  (IdentT (Name.local "ordPair") (args [Var 3; Var 0]))))))))
  in
    {| paraP  := [TySet; TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* Cmp is functional.                                                           *)
Definition IsFunctional : DeclP :=
  let concl :=
    IdentT (Name.local "Functional")
      (args [IdentT (Name.local "Cmp") (args [])])
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.
(* Environment.                                                                 *)

Definition imports : Env := Env.unions
  [ Env.unqualify Equiv.exports
  ; Env.unqualify Functional.exports
  ; Env.unqualify OrdPair.exports
  ].

Definition exports : Env := Env.unions
  [ Env.fromListT
      [ (Name.local "Cmp", Cmp)
      ]
  ; Env.fromListP
      [ (Name.local "Charac2"     , Charac2)
      ; (Name.local "IsFunctional", IsFunctional)
      ]
  ].

Definition env : Env := Env.union imports exports.
