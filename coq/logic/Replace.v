Require Import List.

Require Import Eq.
Require Import Identity.
Require Import Coincide.
Require Import Composition.
Require Import Extensionality. 

(* replace x by y                                                               *)
Definition replace (v:Type) (e:Eq v) (x y:v) (u:v) : v :=
    match e u x with
    | left _    => y    (* if u = x  return y   *)
    | right _   => u    (* otherwise return u   *) 
    end.

Arguments replace {v} _ _ _ _.

Open Scope Composition.


Lemma replace_x_x : forall (v:Type) (e:Eq v) (x:v), 
    replace e x x = id.
Proof.
    intros v e x. apply extensionality. intro u. unfold replace.
    destruct (e u x) as [H|H].
    - subst. reflexivity.
    - reflexivity.
Qed.

Lemma replace_x : forall (v:Type) (e:Eq v) (x y:v),
    replace e x y x = y.
Proof.
    intros v e x y. unfold replace.
    destruct (e x x) as [H|H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
Qed.

Lemma replace_y : forall (v:Type) (e:Eq v) (x y:v),
    replace e x y y = y.
Proof.
    intros v e x y. unfold replace.
    destruct (e y x) as [H|H]; reflexivity.
Qed.


Lemma replace_not_x : forall (v:Type) (e:Eq v) (x y u:v),
    u <> x -> replace e x y u = u.
Proof.
    intros v e x y u H. unfold replace.
    destruct (e u x) as [H'|H'].
    - subst. exfalso. apply H. reflexivity.
    - reflexivity.
Qed.

Lemma replace_trans : forall (v:Type) (e:Eq v) (x y z:v) (ys:list v),
    ~(In y ys) -> coincide ys (replace e y z ; replace e x y) (replace e x z).
Proof.
    intros v e x y z ys H u H'. unfold comp.
    destruct (e u x) as [Hux|Hux], (e u y) as [Huy|Huy], (e u z) as [Huz|Huz]; subst.
    - rewrite replace_x_x. reflexivity.
    - rewrite replace_x_x. reflexivity.
    - rewrite replace_x_x, replace_x, replace_x. reflexivity.
    - rewrite replace_x, replace_x, replace_x. reflexivity.
    - rewrite replace_x_x. reflexivity.
    - exfalso. apply H. assumption. 
    - rewrite replace_y. 
      assert (replace e x y z = z) as E.
        { rewrite replace_not_x. reflexivity. assumption. }
      rewrite E. rewrite replace_y. reflexivity.
    - assert (replace e x y u = u) as E.
        { rewrite replace_not_x. reflexivity. assumption. }
      rewrite E. rewrite replace_not_x, replace_not_x.
          + reflexivity.
          + assumption.
          + assumption.
Qed.


