Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Check.CoreP.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Set.Union.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for set union is well sorted.                           *)
Proposition union : CheckT (Union.env) Union.union.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union.union. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The characterization of set union is well sorted.                            *)
Proposition Charac : CheckP (Union.env) Union.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union.Charac. checkP.
Qed.

(* The class of a union set being the class union is well sorted.               *)
Proposition ToClass : CheckP (Union.env) Union.ToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union.ToClass. checkP.
Qed.

(* The union of the empty set being empty is well sorted.                       *)
Proposition WhenZero : CheckP (Union.env) Union.WhenZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union.WhenZero. checkP.
Qed.

(* The union of a singleton being its element is well sorted.                   *)
Proposition WhenSingleton : CheckP (Union.env) Union.WhenSingleton.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union.WhenSingleton. checkP.
Qed.
