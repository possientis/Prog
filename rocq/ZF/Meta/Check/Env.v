Require Import Coq.Lists.List.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Ty.

(* An environment is checked when all stored declarations are checked.          *)
Definition Check (E:Env) : Prop :=
  (forall (name:Name) (d:DeclT), terms E name  = Some d -> CheckT E d) /\
  (forall (name:Name) (d:DeclP), proofs E name = Some d -> CheckP E d).

(* A checked environment checks every stored term declaration.                  *)
Proposition DeclT : forall (E:Env) (name:Name) (d:DeclT), Check E ->
  terms E name = Some d -> CheckT E d.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E name d H1 H2.
  destruct H1 as [H1 H3].
  apply (H1 name). assumption.
Qed.

(* A checked environment checks every stored proof declaration.                 *)
Proposition DeclP : forall (E:Env) (name:Name) (d:DeclP), Check E ->
  proofs E name = Some d -> CheckP E d.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E name d H1 H2.
  destruct H1 as [H3 H1].
  apply (H1 name). assumption.
Qed.

(* A proof signature has a checked proposition in its parameter context.        *)
Proposition SigP : forall (E:Env) (name:Name) (tys:list Ty) (t:Term), Check E ->
  sigP E name = Some (tys,t) -> Core.CheckT E (rev tys) t TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E name tys t H1 H2.
  unfold sigP in H2.
  destruct (proofs E name) as [d|] eqn:H3. 2: discriminate.
  destruct d as [tys' t' p].
  inversion H2. subst.
  assert (CheckP E {| paraP := tys; conclP := t; bodyP := p |}) as H4. {
    apply (DeclP E name); assumption. }
  unfold ZF.Meta.Check.DeclP.CheckP in H4.
  destruct H4 as [H4 H5].
  apply H4.
Qed.
