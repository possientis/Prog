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

Require Import ZF.Meta.Decl.Class.Relation.Compose.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)


(* The declaration body for class relation composition is well sorted.          *)
Proposition compose : CheckT (Compose.env) Compose.compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.compose. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The ordered-pair characterization of composition is well sorted.             *)
Proposition Charac2 : CheckP (Compose.env) Compose.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.Charac2. checkP.
Qed.

(* Compatibility of composition with equivalence is well sorted.                *)
Proposition EquivCompat : CheckP (Compose.env) Compose.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.EquivCompat. checkP.
Qed.

(* Left compatibility of composition with equivalence is well sorted.           *)
Proposition EquivCompatL : CheckP (Compose.env) Compose.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.EquivCompatL. checkP.
Qed.

(* Right compatibility of composition with equivalence is well sorted.          *)
Proposition EquivCompatR : CheckP (Compose.env) Compose.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.EquivCompatR. checkP.
Qed.

(* Associativity of composition is well sorted.                                 *)
Proposition Assoc : CheckP (Compose.env) Compose.Assoc.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.Assoc. checkP.
Qed.

(* Relationhood of composition is well sorted.                                  *)
Proposition IsRelation : CheckP (Compose.env) Compose.IsRelation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.IsRelation. checkP.
Qed.

(* Functionality of composition is well sorted.                                 *)
Proposition IsFunctional : CheckP (Compose.env) Compose.IsFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.IsFunctional. checkP.
Qed.

(* Converse of composition is well sorted.                                      *)
Proposition Converse : CheckP (Compose.env) Compose.Converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.Converse. checkP.
Qed.

(* Domain inclusion of composition is well sorted.                              *)
Proposition DomainIsSmaller : CheckP (Compose.env) Compose.DomainIsSmaller.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.DomainIsSmaller. checkP.
Qed.

(* Range inclusion of composition is well sorted.                               *)
Proposition RangeIsSmaller : CheckP (Compose.env) Compose.RangeIsSmaller.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.RangeIsSmaller. checkP.
Qed.

(* Domain equality criterion for composition is well sorted.                    *)
Proposition DomainIsSame : CheckP (Compose.env) Compose.DomainIsSame.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.DomainIsSame. checkP.
Qed.

(* Functional domain equality criterion for composition is well sorted.         *)
Proposition DomainIsSame2 : CheckP (Compose.env) Compose.DomainIsSame2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.DomainIsSame2. checkP.
Qed.

(* Range equality criterion for composition is well sorted.                     *)
Proposition RangeIsSame : CheckP (Compose.env) Compose.RangeIsSame.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.RangeIsSame. checkP.
Qed.

(* Injective range equality criterion for composition is well sorted.           *)
Proposition RangeIsSame2 : CheckP (Compose.env) Compose.RangeIsSame2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.RangeIsSame2. checkP.
Qed.

(* Pointwise domain characterization of composition is well sorted.             *)
Proposition FunctionalAtDomainCharac : CheckP (Compose.env) Compose.FunctionalAtDomainCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.FunctionalAtDomainCharac. checkP.
Qed.

(* Functional domain characterization of composition is well sorted.            *)
Proposition FunctionalDomainCharac : CheckP (Compose.env) Compose.FunctionalDomainCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.FunctionalDomainCharac. checkP.
Qed.

(* Pointwise functionality of composition is well sorted.                       *)
Proposition IsFunctionalAt : CheckP (Compose.env) Compose.IsFunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.IsFunctionalAt. checkP.
Qed.

(* Pointwise evaluation of composition is well sorted.                          *)
Proposition FunctionalAtEval : CheckP (Compose.env) Compose.FunctionalAtEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.FunctionalAtEval. checkP.
Qed.

(* Evaluation of functional composition is well sorted.                         *)
Proposition Eval : CheckP (Compose.env) Compose.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.Eval. checkP.
Qed.

(* Inclusion in the Cmp image is well sorted.                                   *)
Proposition ImageUnderCmp : CheckP (Compose.env) Compose.ImageUnderCmp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.ImageUnderCmp. checkP.
Qed.

(* Smallness of composition is well sorted.                                     *)
Proposition IsSmall : CheckP (Compose.env) Compose.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.IsSmall. checkP.
Qed.

(* Image under composition is well sorted.                                      *)
Proposition Image : CheckP (Compose.env) Compose.Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Compose.Image. checkP.
Qed.
