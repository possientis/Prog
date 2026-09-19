Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Equiv.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for toClass maps a set to its membership class.         *)
Proposition toClass : CheckT (Equiv.env) toClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold toClass. checkT.
Qed.

(* The declaration body for equivalence compares two classes pointwise.         *)
Proposition equiv : CheckT (Equiv.env) equiv.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold equiv. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The reflexivity proposition is well sorted using equivalence.                *)
Proposition Refl : CheckP (Equiv.env) Refl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Refl. checkP.
Qed.

(* Equivalence compatibility is a well-sorted proposition.                      *)
Proposition EquivCompat : CheckP (Equiv.env) EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EquivCompat. checkP.
Qed.

(* Left compatibility of equivalence is a well-sorted proposition.              *)
Proposition EquivCompatL : CheckP (Equiv.env) EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EquivCompatL. checkP.
Qed.

(* Right compatibility of equivalence is a well-sorted proposition.             *)
Proposition EquivCompatR : CheckP (Equiv.env) EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EquivCompatR. checkP.
Qed.

(* Symmetry of equivalence is a well-sorted proposition.                        *)
Proposition Sym : CheckP (Equiv.env) Sym.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Sym. checkP.
Qed.

(* Transitivity of equivalence is a well-sorted proposition.                    *)
Proposition Tran : CheckP (Equiv.env) Tran.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Tran. checkP.
Qed.

(* Symmetry of non-equivalence is a well-sorted proposition.                    *)
Proposition NotSym : CheckP (Equiv.env) NotSym.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold NotSym. checkP.
Qed.

(* Equality of sets and equivalence of their classes is well sorted.            *)
Proposition EqualToClass : CheckP (Equiv.env) EqualToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EqualToClass. checkP.
Qed.

(* Inequality of sets and non-equivalence of their classes is well sorted.      *)
Proposition NotEqualToClass : CheckP (Equiv.env) NotEqualToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold NotEqualToClass. checkP.
Qed.

(* Non-equivalence is compatible with equivalence.                              *)
Proposition NotCompat : CheckP (Equiv.env) NotCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold NotCompat. checkP.
Qed.

(* Non-equivalence is left-compatible with equivalence.                         *)
Proposition NotCompatL : CheckP (Equiv.env) NotCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold NotCompatL. checkP.
Qed.

(* Non-equivalence is right-compatible with equivalence.                        *)
Proposition NotCompatR : CheckP (Equiv.env) NotCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold NotCompatR. checkP.
Qed.
