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

Require Import ZF.Meta.Decl.Class.Relation.Restrict.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for relation restriction is well sorted.                *)
Proposition restrict : CheckT (Restrict.env) Restrict.restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.restrict. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The ordered-pair characterization of restriction is well sorted.             *)
Proposition Charac2 : CheckP (Restrict.env) Restrict.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.Charac2. checkP.
Qed.

(* Compatibility of restriction with equivalence is well sorted.                *)
Proposition EquivCompat : CheckP (Restrict.env) Restrict.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.EquivCompat. checkP.
Qed.

(* Left compatibility of restriction with equivalence is well sorted.           *)
Proposition EquivCompatL : CheckP (Restrict.env) Restrict.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.EquivCompatL. checkP.
Qed.

(* Right compatibility of restriction with equivalence is well sorted.          *)
Proposition EquivCompatR : CheckP (Restrict.env) Restrict.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.EquivCompatR. checkP.
Qed.

(* Relationhood of restriction is well sorted.                                  *)
Proposition IsRelation : CheckP (Restrict.env) Restrict.IsRelation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.IsRelation. checkP.
Qed.

(* Functionality of restriction of a functional class is well sorted.           *)
Proposition IsFunctional : CheckP (Restrict.env) Restrict.IsFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.IsFunctional. checkP.
Qed.

(* Domain characterization of restriction is well sorted.                       *)
Proposition DomainOf : CheckP (Restrict.env) Restrict.DomainOf.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.DomainOf. checkP.
Qed.

(* Range characterization of restriction is well sorted.                        *)
Proposition RangeOf : CheckP (Restrict.env) Restrict.RangeOf.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.RangeOf. checkP.
Qed.

(* Range inclusion of restriction is well sorted.                               *)
Proposition RangeIsIncl : CheckP (Restrict.env) Restrict.RangeIsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.RangeIsIncl. checkP.
Qed.

(* Smallness of restriction to a small class is well sorted.                    *)
Proposition IsSmallR : CheckP (Restrict.env) Restrict.IsSmallR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.IsSmallR. checkP.
Qed.

(* Inclusion of restriction in the original class is well sorted.               *)
Proposition IsIncl : CheckP (Restrict.env) Restrict.IsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.IsIncl. checkP.
Qed.

(* Smallness of restriction of a small class is well sorted.                    *)
Proposition IsSmallL : CheckP (Restrict.env) Restrict.IsSmallL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.IsSmallL. checkP.
Qed.

(* The relation characterization by domain restriction is well sorted.          *)
Proposition RelationCharac : CheckP (Restrict.env) Restrict.RelationCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.RelationCharac. checkP.
Qed.

(* The tower property of restriction is well sorted.                            *)
Proposition TowerProperty : CheckP (Restrict.env) Restrict.TowerProperty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.TowerProperty. checkP.
Qed.

(* Smallness below the range of a small restriction is well sorted.             *)
Proposition LesserThanRangeIsSmall :
  CheckP (Restrict.env) Restrict.LesserThanRangeIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.LesserThanRangeIsSmall. checkP.
Qed.

(* Evaluation of a restriction at an included point is well sorted.             *)
Proposition Eval : CheckP (Restrict.env) Restrict.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.Eval. checkP.
Qed.

(* The bounded-range smallness criterion for restriction is well sorted.        *)
Proposition LesserThanRangeOfRestrict :
  CheckP (Restrict.env) Restrict.LesserThanRangeOfRestrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.LesserThanRangeOfRestrict. checkP.
Qed.

(* Restriction to an empty class is well sorted.                                *)
Proposition WhenZero : CheckP (Restrict.env) Restrict.WhenZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.WhenZero. checkP.
Qed.
