Require Import List.

Require Import Eq.
Require Import Identity.
Require Import Injective.
Require Import Coincide.
Require Import Composition.
Require Import Extensionality. 

(* replace x by y                                                               *)
Definition replace (v:Type) (e:Eq v) (x y:v) (u:v) : v :=
    match eqDec u x with
    | left _    => y    (* if u = x  return y   *)
    | right _   => u    (* otherwise return u   *) 
    end.

Arguments replace {v} {e} _ _ _.

Open Scope Composition.


Lemma replace_x_x : forall (v:Type) (e:Eq v) (x:v), 
    replace x x = id.
Proof.
    intros v e x. apply extensionality. intro u. unfold replace.
    destruct (eqDec u x) as [H|H].
    - subst. reflexivity.
    - reflexivity.
Qed.

Lemma replace_x : forall (v:Type) (e:Eq v) (x y:v),
    replace x y x = y.
Proof.
    intros v e x y. unfold replace.
    destruct (eqDec x x) as [H|H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
Qed.

Lemma replace_y : forall (v:Type) (e:Eq v) (x y:v),
    replace x y y = y.
Proof.
    intros v e x y. unfold replace.
    destruct (eqDec y x) as [H|H]; reflexivity.
Qed.


Lemma replace_not_x : forall (v:Type) (e:Eq v) (x y u:v),
    u <> x -> replace x y u = u.
Proof.
    intros v e x y u H. unfold replace.
    destruct (eqDec u x) as [H'|H'].
    - subst. exfalso. apply H. reflexivity.
    - reflexivity.
Qed.

Lemma replace_trans : forall (v:Type) (e:Eq v) (x y z:v) (ys:list v),
    ~(In y ys) -> coincide ys (replace y z ; replace x y) (replace x z).
Proof.
    intros v e x y z ys H u H'. unfold comp.
    destruct (eqDec u x) as [Hux|Hux], 
             (eqDec u y) as [Huy|Huy], 
             (eqDec u z) as [Huz|Huz]; subst.
    - rewrite replace_x_x. reflexivity.
    - rewrite replace_x_x. reflexivity.
    - rewrite replace_x_x, replace_x, replace_x. reflexivity.
    - rewrite replace_x, replace_x, replace_x. reflexivity.
    - rewrite replace_x_x. reflexivity.
    - exfalso. apply H. assumption. 
    - rewrite replace_y. 
      assert (replace x y z = z) as E.
        { rewrite replace_not_x. reflexivity. assumption. }
      rewrite E. rewrite replace_y. reflexivity.
    - assert (replace x y u = u) as E.
        { rewrite replace_not_x. reflexivity. assumption. }
      rewrite E. rewrite replace_not_x, replace_not_x.
          + reflexivity.
          + assumption.
          + assumption.
Qed.

Lemma replace_inj : forall (v:Type) (e:Eq v) (x y:v) (ys:list v),
    ~In y ys -> injective_on ys (replace x y).
Proof.
    intros v e x y ys Hy s t Hs Ht H.
    destruct (eqDec s x) as [Hsx|Hsx], (eqDec t x) as [Htx|Htx]; subst.
    - reflexivity.
    - rewrite replace_x in H. 
      rewrite replace_not_x in H.
        + subst. exfalso. apply Hy, Ht.
        + assumption.
    - rewrite replace_x in H. 
      rewrite replace_not_x in H.
        + subst. exfalso. apply Hy, Hs.
        + assumption.
    - rewrite replace_not_x in H.
        + rewrite replace_not_x in H; assumption.
        + assumption.
Qed.
