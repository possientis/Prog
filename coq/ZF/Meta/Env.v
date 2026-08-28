Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Sigs.

Import ListNotations.

(* A global environment maps names to term declarations.                        *)
Definition Env : Type := string -> option Decl.

(* The empty environment has no declarations.                                   *)
Definition empty : Env := fun _ => None.

(* A singleton environment maps one name to one term declaration.               *)
Definition single (name:string) (d:Decl) : Env := fun key =>
  if String.eqb key name then Some d else None.

(* The union of two environments searches the left environment first.           *)
Definition union (e1 e2:Env) : Env := fun name =>
  match e1 name with
  | Some d => Some d
  | None   => e2 name
  end.

(* The union of a list of environments prefers earlier environments.            *)
Fixpoint unions (es:list Env) : Env :=
  match es with
  | []      => empty
  | e :: es => union e (unions es)
  end.

(* A list of named term declarations becomes an environment with earlier names. *)
Fixpoint fromList (ds:list (string * Decl)) : Env :=
  match ds with
  | []             => empty
  | (name,d) :: ds => union (single name d) (fromList ds)
  end.

(* The signature view forgets term declaration bodies.                          *)
Definition toSigs (e:Env) : Sigs := fun name =>
  match e name with
  | Some d => Some (Decl.signature d)
  | None   => None
  end.
