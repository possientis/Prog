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

Require Import ZF.Meta.Decl.Set.Empty.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for the empty set is well sorted.                       *)
Proposition empty : CheckT (Empty.env) Empty.empty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.empty. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The class of the empty set being empty is well sorted.                       *)
Proposition ToClass : CheckP (Empty.env) Empty.ToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.ToClass. checkP.
Qed.

(* The characterization of the empty set is well sorted.                        *)
Proposition Charac : CheckP (Empty.env) Empty.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.Charac. checkP.
Qed.

(* The empty set being included in every set is well sorted.                    *)
Proposition IsIncl : CheckP (Empty.env) Empty.IsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.IsIncl. checkP.
Qed.

(* The empty set having no elements is well sorted.                             *)
Proposition NoElem : CheckP (Empty.env) Empty.NoElem.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.NoElem. checkP.
Qed.

(* The criterion for set non-emptiness is well sorted.                          *)
Proposition HasElem : CheckP (Empty.env) Empty.HasElem.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.HasElem. checkP.
Qed.

(* The criterion for set emptiness is well sorted.                              *)
Proposition HasNoElem : CheckP (Empty.env) Empty.HasNoElem.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.HasNoElem. checkP.
Qed.

(* The no-element emptiness criterion is well sorted.                           *)
Proposition WhenNoElem : CheckP (Empty.env) Empty.WhenNoElem.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.WhenNoElem. checkP.
Qed.

(* Pairs being non-empty is well sorted.                                        *)
Proposition PairIsNotEmpty : CheckP (Empty.env) Empty.PairIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.PairIsNotEmpty. checkP.
Qed.

(* Ordered pairs being non-empty is well sorted.                                *)
Proposition OrdPairIsNotEmpty : CheckP (Empty.env) Empty.OrdPairIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.OrdPairIsNotEmpty. checkP.
Qed.

(* Singletons being non-empty is well sorted.                                   *)
Proposition SingletonIsNotEmpty : CheckP (Empty.env) Empty.SingletonIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.SingletonIsNotEmpty. checkP.
Qed.

(* The class criterion for set emptiness is well sorted.                        *)
Proposition EmptyToClass : CheckP (Empty.env) Empty.EmptyToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.EmptyToClass. checkP.
Qed.

(* The class criterion for set non-emptiness is well sorted.                    *)
Proposition NotEmptyToClass : CheckP (Empty.env) Empty.NotEmptyToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.NotEmptyToClass. checkP.
Qed.

(* Subsets of the empty set being empty is well sorted.                         *)
Proposition WhenIncl : CheckP (Empty.env) Empty.WhenIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.WhenIncl. checkP.
Qed.
