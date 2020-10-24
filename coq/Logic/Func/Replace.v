Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Func.Identity.
Require Import Logic.Func.Injective.
Require Import Logic.Func.Composition.

Require Import Logic.Axiom.Extensionality. 

(* replace x by y                                                               *)
Definition replace (v:Type) (e:Eq v) (x y:v) (u:v) : v :=
    match eqDec u x with
    | left _    => y    (* if u = x  return y   *)
    | right _   => u    (* otherwise return u   *) 
    end.

Arguments replace {v} {e}.

Notation "y // x" := (replace x y)
    (at level 70, no associativity) : Replace_scope.

Open Scope Replace_scope.

Definition replace2 (v:Type) (e:Eq v) (x y x' y':v) (u:v) : v :=
    match eqDec u x with
    | left _    => x'       (* if u = x  return x'  *)
    | right _   =>
        match eqDec u y with
        | left _    => y'   (* if u = y  return y'  *)
        | right _   => u    (* otherwise return u   *)
        end
    end.

Arguments replace2 {v} {e}.

Lemma replace_x_x : forall (v:Type) (e:Eq v) (x:v), 
    (x // x) = id.
Proof.
    intros v e x. apply extensionality. intro u. unfold replace.
    destruct (eqDec u x) as [H|H].
    - subst. reflexivity.
    - reflexivity.
Qed.

Lemma replace_x : forall (v:Type) (e:Eq v) (x y:v),
    (y // x) x = y.
Proof.
    intros v e x y. unfold replace.
    destruct (eqDec x x) as [H|H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
Qed.

Lemma replace_y : forall (v:Type) (e:Eq v) (x y:v),
    (y // x) y = y.
Proof.
    intros v e x y. unfold replace.
    destruct (eqDec y x) as [H|H]; reflexivity.
Qed.


Lemma replace_not_x : forall (v:Type) (e:Eq v) (x y u:v),
    u <> x -> (y // x) u = u.
Proof.
    intros v e x y u H. unfold replace.
    destruct (eqDec u x) as [H'|H'].
    - subst. exfalso. apply H. reflexivity.
    - reflexivity.
Qed.

Lemma replace_injective : forall (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (x y:v),
    injective f -> f ; (y // x) = (f y // f x) ; f.
Proof.
    intros v w e e' f x y H1. apply extensionality. intro u. unfold comp, replace. 
    destruct (eqDec u x) as [H2|H2]; destruct (eqDec (f u) (f x)) as [H3|H3].
    - reflexivity.
    - subst. exfalso. apply H3. reflexivity.
    - exfalso. apply H2, H1. assumption.
    - reflexivity.
Qed.
