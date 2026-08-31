Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Classic.

(* Double negation is a well-typed proof declaration.                           *)
Proposition DoubleNegation : CheckDeclP (Classic.env) DoubleNegation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* The parameter is a proposition, so both the negated assumption and the     *)
  (* resulting conclusion are propositions.                                     *)
  assert (CheckT Classic.env (ctxP DoubleNegation)
    (conclP DoubleNegation) TyProp) as H1. {
    apply CheckImp.
    - apply CheckNot, CheckNot. apply CheckVar. reflexivity.
    - apply CheckVar. reflexivity. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.

(* Negated universality is a well-typed proof declaration.                      *)
Proposition NotForAll : CheckDeclP (Classic.env) NotForAll.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* A class predicate applied to the bound set variable is a proposition, so   *)
  (* both sides of the equivalence are propositions.                            *)
  assert (CheckT Classic.env (ctxP NotForAll)
    (conclP NotForAll) TyProp) as H1. {
    apply CheckIff.
    - apply CheckNot, CheckAll, CheckApp.
      + apply CheckVar. reflexivity.
      + apply CheckVar. reflexivity.
    - apply CheckEx, CheckNot, CheckApp.
      + apply CheckVar. reflexivity.
      + apply CheckVar. reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Negated universal negation is a well-typed proof declaration.                *)
Proposition NotForAllNot : CheckDeclP (Classic.env) NotForAllNot.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* The universally quantified negation and the existential witness both come  *)
  (* from applying the class predicate to a set.                                *)
  assert (CheckT Classic.env (ctxP NotForAllNot)
    (conclP NotForAllNot) TyProp) as H1. {
    apply CheckIff.
    - apply CheckNot, CheckAll, CheckNot, CheckApp.
      + apply CheckVar. reflexivity.
      + apply CheckVar. reflexivity.
    - apply CheckEx, CheckApp.
      + apply CheckVar. reflexivity.
      + apply CheckVar. reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The law of excluded middle is a well-typed proof declaration.                *)
Proposition LawExcludedMiddle : CheckDeclP (Classic.env) LawExcludedMiddle.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* The single parameter is a proposition, and its negation is also a          *)
  (* proposition, hence their disjunction is a proposition.                     *)
  assert (CheckT Classic.env (ctxP LawExcludedMiddle)
    (conclP LawExcludedMiddle) TyProp) as H1. {
    apply CheckOr.
    - apply CheckVar. reflexivity.
    - apply CheckNot. apply CheckVar. reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
