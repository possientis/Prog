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

Require Import ZF.Meta.Decl.Class.Relation.Converse.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for relation converse is well sorted.                   *)
Proposition converse : CheckT (Converse.env) Converse.converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.converse. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The forward converse characterization is well sorted.                        *)
Proposition Charac2 : CheckP (Converse.env) Converse.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.Charac2. checkP.
Qed.

(* The reverse converse characterization is well sorted.                        *)
Proposition Charac2Rev : CheckP (Converse.env) Converse.Charac2Rev.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.Charac2Rev. checkP.
Qed.

(* Compatibility of relation converse with equivalence is well sorted.          *)
Proposition EquivCompat : CheckP (Converse.env) Converse.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.EquivCompat. checkP.
Qed.

(* Compatibility of relation converse with inclusion is well sorted.            *)
Proposition InclCompat : CheckP (Converse.env) Converse.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.InclCompat. checkP.
Qed.

(* The image-under-switch characterization is well sorted.                      *)
Proposition ImageUnderSwitch : CheckP (Converse.env) Converse.ImageUnderSwitch.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.ImageUnderSwitch. checkP.
Qed.

(* Smallness of relation converse over a small relation is well sorted.         *)
Proposition IsSmall : CheckP (Converse.env) Converse.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.IsSmall. checkP.
Qed.

(* Relationhood of relation converse is well sorted.                            *)
Proposition IsRelation : CheckP (Converse.env) Converse.IsRelation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.IsRelation. checkP.
Qed.

(* Inclusion of the double converse into the original class is well sorted.     *)
Proposition IsIncl : CheckP (Converse.env) Converse.IsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.IsIncl. checkP.
Qed.

(* The idempotence characterization of relations is well sorted.                *)
Proposition IsIdempotent : CheckP (Converse.env) Converse.IsIdempotent.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.IsIdempotent. checkP.
Qed.

(* The ordered-pair subclass converse characterization is well sorted.          *)
Proposition IsConverseOfOrderedPairs :
  CheckP (Converse.env) Converse.IsConverseOfOrderedPairs.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.IsConverseOfOrderedPairs. checkP.
Qed.

(* The converse-domain/range characterization is well sorted.                   *)
Proposition Domain : CheckP (Converse.env) Converse.Domain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.Domain. checkP.
Qed.

(* The converse-range/domain characterization is well sorted.                   *)
Proposition Range : CheckP (Converse.env) Converse.Range.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.Range. checkP.
Qed.

(* The converse-functional criterion is well sorted.                            *)
Proposition WhenFunctional : CheckP (Converse.env) Converse.WhenFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.WhenFunctional. checkP.
Qed.

(* The functional-converse image/intersection theorem is well sorted.           *)
Proposition Inter2Image : CheckP (Converse.env) Converse.Inter2Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Converse.Inter2Image. checkP.
Qed.
