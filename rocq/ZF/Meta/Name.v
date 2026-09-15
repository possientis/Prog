Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Local Definition Qualifier : Type := option string.

Local Definition LocalName : Type := string.

Record Name : Type := mkName
  { qualifier : Qualifier
  ; localName : LocalName
  }.

Definition local (s:LocalName) : Name :=
  mkName None s.

Definition qualified (q:string) (s:LocalName) : Name :=
  mkName (Some q) s.

Local Definition qualifierEqb (q r:Qualifier) : bool :=
  match q, r with
  | None   , None    => true
  | Some q , Some r  => String.eqb q r
  | _      , _       => false
  end.

Definition eqb (x y:Name) : bool :=
  qualifierEqb (qualifier x) (qualifier y) &&
    String.eqb (localName x) (localName y).
