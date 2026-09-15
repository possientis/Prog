Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Name.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Ty.
Require Import ZF.Meta.Syntax.

Import ListNotations.
Open Scope string_scope.

(* A global environment has separate term and proof declaration namespaces.     *)
Record Env : Type := mkEnv
  { terms  : Name -> option DeclT
  ; proofs : Name -> option DeclP
  }.

Definition sigT (e:Env) (name:Name) : option (list Ty * Ty) :=
  match terms e name with
  | None   => None
  | Some d => Some (paraT d, resT d)
  end.

Definition sigP (e:Env) (name:Name) : option (list Ty * Term) :=
  match proofs e name with
  | None   => None
  | Some d => Some (paraP d, conclP d)
  end.

(* The empty environment has no declarations.                                   *)
Definition empty : Env :=
  {| terms  := fun _ => None
   ; proofs := fun _ => None |}.

(* A singleton environment maps one name to one term declaration.               *)
Definition singleT (name:Name) (d:DeclT) : Env :=
  {| terms := fun key => if Name.eqb key name then Some d else None
   ; proofs := fun _ => None |}.

(* A singleton environment maps one name to one proof declaration.              *)
Definition singleP (name:Name) (d:DeclP) : Env :=
  {| terms := fun _ => None
   ; proofs := fun key => if Name.eqb key name then Some d else None |}.

(* The union of two environments searches the left environment first.           *)
Definition union (e1 e2:Env) : Env :=
  {| terms := fun name =>
       match terms e1 name with
       | Some d => Some d
       | None   => terms e2 name
       end
   ; proofs := fun name =>
       match proofs e1 name with
       | Some d => Some d
       | None   => proofs e2 name
       end |}.

(* An imported environment exposes its declarations without qualification.      *)
Definition unqualify (e:Env) : Env :=
  {| terms := fun name =>
       match Name.qualifier name with
       | None   => terms e (Name.local (Name.localName name))
       | Some _ => None
       end
   ; proofs := fun name =>
       match Name.qualifier name with
       | None   => proofs e (Name.local (Name.localName name))
       | Some _ => None
       end |}.

(* An imported environment exposes its declarations under one qualifier.        *)
Definition qualifyAs (q:string) (e:Env) : Env :=
  {| terms := fun name =>
       match Name.qualifier name with
       | Some r =>
           if String.eqb r q then terms e (Name.local (Name.localName name))
           else None
       | None   => None
       end
   ; proofs := fun name =>
       match Name.qualifier name with
       | Some r =>
           if String.eqb r q then proofs e (Name.local (Name.localName name))
           else None
       | None   => None
       end |}.

(* The union of a list of environments prefers earlier environments.            *)
Fixpoint unions (es:list Env) : Env :=
  match es with
  | []      => empty
  | e :: es => union e (unions es)
  end.

(* A list of named term declarations becomes an environment with earlier names. *)
Fixpoint fromListT (ds:list (Name * DeclT)) : Env :=
  match ds with
  | []             => empty
  | (name,d) :: ds => union (singleT name d) (fromListT ds)
  end.

(* A list of named proof declarations becomes an environment with earlier names.*)
Fixpoint fromListP (ds:list (Name * DeclP)) : Env :=
  match ds with
  | []             => empty
  | (name,d) :: ds => union (singleP name d) (fromListP ds)
  end.
