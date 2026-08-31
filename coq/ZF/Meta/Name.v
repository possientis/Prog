Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

Definition ModuleName : Type := list string.

Definition LocalName : Type := string.

Record Name : Type := mkName
  { moduleName : ModuleName
  ; localName  : LocalName
  }.

Definition name (ms:ModuleName) (s:LocalName) : Name :=
  mkName ms s.

Definition local (s:LocalName) : Name :=
  name [] s.

Fixpoint moduleNameEqb (ms ns:ModuleName) : bool :=
  match ms, ns with
  | []      , []       => true
  | m :: ms , n :: ns  => String.eqb m n && moduleNameEqb ms ns
  | _       , _        => false
  end.

Definition eqb (x y:Name) : bool :=
  moduleNameEqb (moduleName x) (moduleName y) &&
    String.eqb (localName x) (localName y).
