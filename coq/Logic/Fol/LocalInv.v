Require Import List.
Import ListNotations.

Require Import Logic.Class.Eq.

Require Import Logic.List.In.
Require Import Logic.List.Nil.
Require Import Logic.List.Remove.
Require Import Logic.List.Include.
Require Import Logic.List.Intersect.
Require Import Logic.List.Difference.

Require Import Logic.Fol.Dmap.
Require Import Logic.Fol.Free.
Require Import Logic.Fol.Bound.
Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.
Require Import Logic.Fol.Functor.

(*
Lemma localInv_lemma : 
    forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(v0 v1:list v)(g0 g1:w -> v),
        forall (xs:list v) (p:P v), 
            (forall (x:v), (x :: v0) -> g0 (f x) = x)   ->
            (forall (x:v), (x :: v1) -> g1 (f x) = x)   ->
            (bnd p ++ xs <= v0)                         ->
            (Fr p  \\ xs <= v1)                         -> 
            valid f p                                   ->
            (map f xs /\ map f (Fr p \\ xs)) = []       ->
                dmap_ g0 g1 (map f xs) (fmap f p) = p.
Proof.
    intros v w e e' f v0 v1 g0 g1 xs p H1 H2. revert p xs.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; intros xs H3 H4 H5 H6; simpl.
    - reflexivity.
    - assert (h_ g0 g1 (map f xs) (f x) = x) as G1.
        { unfold h_. destruct (in_dec eqDec x xs) as [G1|G1].
            { assert (f x :: map f xs) as G2.
                { apply in_map_iff. exists x. split. 
                    { reflexivity. } 
                    { assumption. }}
              destruct (in_dec eqDec (f x) (map f xs)) as [G3|G3].
                { apply H1. apply H3. apply in_or_app. right. assumption. }
                { apply G3 in G2. contradiction. }}
            { assert (~ f x :: map f xs) as G2.
                { intros G2. assert (f x :: map f (Fr (Elem x y) \\ xs)) as G3.
                    { apply in_map_iff. exists x. split.
                        { reflexivity. }
                        { apply diff_charac. split.
                            { left. reflexivity. }
                            { assumption. }}}
                  assert (f x :: []) as G4. 
                      { rewrite <- H6.  apply inter_charac. split; assumption. }
                  inversion G4. }
              destruct (in_dec eqDec (f x) (map f xs)) as [G3|G3].
                  { apply G2 in G3. contradiction. }
                  { apply H2. apply H4. apply diff_charac. split.
                      { left. reflexivity. }
                      { assumption. }}}}
     assert (h_ g0 g1 (map f xs) (f y) = y) as G1'.
        { unfold h_. destruct (in_dec eqDec y xs) as [G1'|G1'].
            { assert (f y :: map f xs) as G2.
                { apply in_map_iff. exists y. split. 
                    { reflexivity. } 
                    { assumption. }}
              destruct (in_dec eqDec (f y) (map f xs)) as [G3|G3].
                { apply H1. apply H3. apply in_or_app. right. assumption. }
                { apply G3 in G2. contradiction. }}
            { assert (~ f y :: map f xs) as G2.
                { intros G2. assert (f y :: map f (Fr (Elem x y) \\ xs)) as G3.
                    { apply in_map_iff. exists y. split.
                        { reflexivity. }
                        { apply diff_charac. split.
                            { right. left. reflexivity. }
                            { assumption. }}}
                  assert (f y :: []) as G4. 
                      { rewrite <- H6.  apply inter_charac. split; assumption. }
                  inversion G4. }
              destruct (in_dec eqDec (f y) (map f xs)) as [G3|G3].
                  { apply G2 in G3. contradiction. }
                  { apply H2. apply H4. apply diff_charac. split.
                      { right. left. reflexivity. }
                      { assumption. }}}}
      rewrite G1, G1'. reflexivity.
    - simpl in H3. simpl in H4.  rewrite diff_distrib_app_r in H4.
      apply valid_imp in H5. destruct H5 as [H7 H8]. simpl in H6.
      rewrite diff_distrib_app_r in H6. rewrite map_app in H6.
      apply inter_app_nil_l in H6. destruct H6 as [H9 H10].
      rewrite <- app_assoc in H3. 
      rewrite IH1, IH2; try (assumption).
        + reflexivity.
        + apply incl_tran with (bnd p1 ++ bnd p2 ++ xs).
            { apply incl_appr, incl_refl. }
            { assumption. }
        + apply incl_tran with (Fr p1 \\ xs ++ Fr p2 \\ xs).
            { apply incl_appr, incl_refl. }
            { assumption. }
        + apply incl_tran with (bnd p1 ++ bnd p2 ++ xs).
            { apply incl_app2.
                { apply incl_refl. }
                { apply incl_appr, incl_refl. }}
            { assumption. }
        + apply incl_tran with (Fr p1 \\ xs ++ Fr p2 \\ xs).
            { apply incl_appl, incl_refl. }
            { assumption. }
    - simpl in H3. rewrite <- map_cons. apply valid_all in H5.
      destruct H5 as [H5 H8].
      rewrite IH1.
        + rewrite H1.
            { reflexivity. }
            { apply H3. left. reflexivity. }
        + intros z H7. apply in_app_or in H7. destruct H7 as [H7|H7]; apply H3.
            { right. apply in_or_app. left. assumption. }
            { destruct H7 as [H7|H7].
                { subst. left. reflexivity. }
                { right. apply in_or_app. right. assumption. }}
        + simpl in H4. rewrite remove_diff in H4. 
          rewrite <- diff_distrib_app_l' in H4. simpl in H4. assumption.
        + assumption.
        + apply nil_charac. intros y' H7. apply inter_charac in H7.
          destruct H7 as [H7 H9]. rewrite map_cons in H7. destruct H7 as [H7|H7].
            { apply in_map_iff in H9. destruct H9 as [y [H9 H10]].
             apply (H8 y). 
                { simpl. rewrite remove_diff. apply diff_charac in H10.
                  destruct H10 as [H10 H11]. apply diff_charac. split.
                    { assumption. }
                    { intros H12.  apply H11. left. destruct H12 as [H12|H12].
                        { assumption. }
                        { inversion H12. }}}
                { rewrite H7, H9. reflexivity. }}
            {

Show.
*)
