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

Require Import ZF.Meta.Decl.Class.Prod.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for class products is well sorted.                      *)
Proposition prod : CheckT (Prod.env) Prod.prod.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.prod. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The binary characterization of class products is well sorted.                *)
Proposition Charac2 : CheckP (Prod.env) Prod.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.Charac2. checkP.
Qed.

(* Compatibility of class products with equivalence is well sorted.             *)
Proposition EquivCompat : CheckP (Prod.env) Prod.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.EquivCompat. checkP.
Qed.

(* Left compatibility of class products with equivalence is well sorted.        *)
Proposition EquivCompatL : CheckP (Prod.env) Prod.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.EquivCompatL. checkP.
Qed.

(* Right compatibility of class products with equivalence is well sorted.       *)
Proposition EquivCompatR : CheckP (Prod.env) Prod.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.EquivCompatR. checkP.
Qed.

(* Compatibility of class products with inclusion is well sorted.               *)
Proposition InclCompat : CheckP (Prod.env) Prod.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.InclCompat. checkP.
Qed.

(* Left compatibility of class products with inclusion is well sorted.          *)
Proposition InclCompatL : CheckP (Prod.env) Prod.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.InclCompatL. checkP.
Qed.

(* Right compatibility of class products with inclusion is well sorted.         *)
Proposition InclCompatR : CheckP (Prod.env) Prod.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.InclCompatR. checkP.
Qed.

(* The relation-product inclusion theorem is well sorted.                       *)
Proposition IsInclRel : CheckP (Prod.env) Prod.IsInclRel.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.IsInclRel. checkP.
Qed.

(* The function-product inclusion theorem is well sorted.                       *)
Proposition IsInclFun : CheckP (Prod.env) Prod.IsInclFun.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.IsInclFun. checkP.
Qed.

(* Smallness of class products is well sorted.                                  *)
Proposition IsSmall : CheckP (Prod.env) Prod.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.IsSmall. checkP.
Qed.

(* The switch-image characterization is well sorted.                            *)
Proposition ImageUnderSwitch : CheckP (Prod.env) Prod.ImageUnderSwitch.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.ImageUnderSwitch. checkP.
Qed.

(* Commuted smallness of class products is well sorted.                         *)
Proposition IsSmallComm : CheckP (Prod.env) Prod.IsSmallComm.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.IsSmallComm. checkP.
Qed.

(* Properness of class products is well sorted.                                 *)
Proposition IsProper : CheckP (Prod.env) Prod.IsProper.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.IsProper. checkP.
Qed.

(* Properness of class squares is well sorted.                                  *)
Proposition SquareIsProper : CheckP (Prod.env) Prod.SquareIsProper.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.SquareIsProper. checkP.
Qed.

(* The intersection-of-products characterization is well sorted.                *)
Proposition Inter2 : CheckP (Prod.env) Prod.Inter2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Prod.Inter2. checkP.
Qed.

