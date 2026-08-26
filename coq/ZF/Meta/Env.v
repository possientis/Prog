Require Import Coq.Strings.String.

Require Import ZF.Meta.Decl.
Require Import ZF.Meta.Sigs.

(* A global environment maps names to declarations.                             *)
Definition Env : Type := string -> option Decl.

(* The empty environment has no declarations.                                   *)
Definition empty : Env := fun _ => None.

(* The signature view forgets declaration bodies.                               *)
Definition toSigs (e:Env) : Sigs := fun name =>
  match e name with
  | Some d => Some (Decl.signature d)
  | None   => None
  end.
