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

Require Import ZF.Meta.Decl.Class.DiffBySet.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)


(* The declaration body for class-by-set difference is well sorted.             *)
Proposition diff : CheckT (DiffBySet.env) DiffBySet.diff.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.diff. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The characterization of class-by-set difference is well sorted.              *)
Proposition Charac : CheckP (DiffBySet.env) DiffBySet.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.Charac. checkP.
Qed.

(* Compatibility of class-by-set difference with equivalence is well sorted.    *)
Proposition EquivCompat : CheckP (DiffBySet.env) DiffBySet.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.EquivCompat. checkP.
Qed.

(* Left compatibility of class-by-set difference with inclusion is well sorted. *)
Proposition InclCompatL : CheckP (DiffBySet.env) DiffBySet.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.InclCompatL. checkP.
Qed.

(* Right compatibility of class-by-set difference with inclusion is well sorted.*)
Proposition InclCompatR : CheckP (DiffBySet.env) DiffBySet.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.InclCompatR. checkP.
Qed.

(* Left projection inclusion of class-by-set difference is well sorted.         *)
Proposition IsInclL : CheckP (DiffBySet.env) DiffBySet.IsInclL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.IsInclL. checkP.
Qed.

(* Right projection inclusion of class-by-set difference is well sorted.        *)
Proposition IsInclR : CheckP (DiffBySet.env) DiffBySet.IsInclR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.IsInclR. checkP.
Qed.

(* The empty-set right identity for class-by-set difference is well sorted.     *)
Proposition IdentityR : CheckP (DiffBySet.env) DiffBySet.IdentityR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.IdentityR. checkP.
Qed.

(* Smallness of class-by-set difference is well sorted.                         *)
Proposition IsSmall : CheckP (DiffBySet.env) DiffBySet.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.IsSmall. checkP.
Qed.

(* Properness of class-by-set difference is well sorted.                        *)
Proposition IsProper : CheckP (DiffBySet.env) DiffBySet.IsProper.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.IsProper. checkP.
Qed.

(* The zero criterion for class-by-set difference is well sorted.               *)
Proposition WhenZero : CheckP (DiffBySet.env) DiffBySet.WhenZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.WhenZero. checkP.
Qed.

(* The nonzero criterion for class-by-set difference is well sorted.            *)
Proposition WhenNotZero : CheckP (DiffBySet.env) DiffBySet.WhenNotZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.WhenNotZero. checkP.
Qed.

(* The included-set nonzero criterion is well sorted.                           *)
Proposition WhenIncl : CheckP (DiffBySet.env) DiffBySet.WhenIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.WhenIncl. checkP.
Qed.

(* The proper-inclusion nonzero criterion is well sorted.                       *)
Proposition WhenLess : CheckP (DiffBySet.env) DiffBySet.WhenLess.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.WhenLess. checkP.
Qed.

(* Right distribution over set union is well sorted.                            *)
Proposition UnionR : CheckP (DiffBySet.env) DiffBySet.UnionR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.UnionR. checkP.
Qed.

(* Image compatibility of class-by-set difference is well sorted.               *)
Proposition Image : CheckP (DiffBySet.env) DiffBySet.Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DiffBySet.Image. checkP.
Qed.
