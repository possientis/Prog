Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Sigs.
Require Import ZF.Meta.Term.Decl.

Import ListNotations.

(* A global environment has separate term and proof declaration namespaces.     *)
Record Env : Type := mkEnv
  { terms  : string -> option DeclT
  ; proofs : string -> option DeclP
  }.

Coercion terms : Env >-> Funclass.

(* The empty environment has no declarations.                                   *)
Definition empty : Env :=
  {| terms  := fun _ => None
   ; proofs := fun _ => None |}.

(* A singleton environment maps one name to one term declaration.               *)
Definition singleT (name:string) (d:DeclT) : Env :=
  {| terms := fun key => if String.eqb key name then Some d else None
   ; proofs := fun _ => None |}.

(* A singleton environment maps one name to one proof declaration.              *)
Definition singleP (name:string) (d:DeclP) : Env :=
  {| terms := fun _ => None
   ; proofs := fun key => if String.eqb key name then Some d else None |}.

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

(* The union of a list of environments prefers earlier environments.            *)
Fixpoint unions (es:list Env) : Env :=
  match es with
  | []      => empty
  | e :: es => union e (unions es)
  end.

(* A list of named term declarations becomes an environment with earlier names. *)
Fixpoint fromListT (ds:list (string * DeclT)) : Env :=
  match ds with
  | []             => empty
  | (name,d) :: ds => union (singleT name d) (fromListT ds)
  end.

(* A list of named proof declarations becomes an environment with earlier names.*)
Fixpoint fromListP (ds:list (string * DeclP)) : Env :=
  match ds with
  | []             => empty
  | (name,d) :: ds => union (singleP name d) (fromListP ds)
  end.

(* The signature view forgets term declaration bodies.                          *)
Definition toSigs (e:Env) : Sigs := fun name =>
  match terms e name with
  | Some d => Some (signatureT d)
  | None   => None
  end.
