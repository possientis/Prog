Require Import List.
Import ListNotations.

Require Import Logic.Class.Eq.

Require Import Logic.List.In.
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
    -

Show.
*)
