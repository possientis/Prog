Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Func.Replace.
Require Import Logic.Func.Permute.
Require Import Logic.Func.Identity.
Require Import Logic.Func.Composition.

Require Import Logic.List.In.
Require Import Logic.List.Coincide.
Require Import Logic.List.InjectiveOn.

Lemma replace_trans : forall (v:Type) (e:Eq v) (x y z:v) (ys:list v),
    ~ y :: ys -> coincide ys ((z // y) ; (y // x)) (z // x).
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
    ~ y :: ys -> injective_on ys (y // x).
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

Lemma replace_permute : forall (v:Type) (e:Eq v) (x y:v) (ys: list v),
    ~ y :: ys -> coincide ys (y // x) (y <:> x).
Proof.
    intros v e x y ys H. unfold coincide. intros u H'.
    destruct    (eqDec u x) as [Hux|Hux] eqn:Eux, 
                (eqDec u y) as [Huy|Huy] eqn:Euy; 
    subst; unfold permute, replace.
    - exfalso. apply H. assumption.
    - destruct (eqDec x x) as [Hxx|Hxx].
        + reflexivity.
        + destruct (eqDec x y); reflexivity. 
    - exfalso. apply H. assumption.
    - rewrite Eux, Euy. reflexivity.
Qed.

