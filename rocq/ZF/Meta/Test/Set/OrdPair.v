Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Set.OrdPair.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The ordered pair declaration pairs a singleton with an unordered pair.       *)
Proposition ordPair : CheckT (OrdPair.env) OrdPair.ordPair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OrdPair.ordPair. checkT.
Qed.

(* The characterization proposition is well sorted.                             *)
Proposition Charac : CheckP (OrdPair.env) OrdPair.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OrdPair.Charac. checkP.
Qed.

(* Singleton equality with a pair forces equality with both pair members.       *)
Proposition ABC : CheckP (OrdPair.env) OrdPair.ABC.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OrdPair.ABC. checkP.
Qed.

(* Equality of ordered pairs forces equality of their respective components.    *)
Proposition Equal : CheckP (OrdPair.env) OrdPair.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OrdPair.Equal. checkP.
Qed.
