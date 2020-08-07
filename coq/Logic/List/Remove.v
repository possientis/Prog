Require Import List.  
Import ListNotations.

Require Import Logic.Class.Eq.

Require Import Logic.List.In.
Require Import Logic.List.Include.
Require Import Logic.List.InjectiveOn.
Require Import Logic.List.Difference.

Fixpoint remove (v:Type) (e:Eq v) (x:v) (xs:list v) : list v :=
    match xs with
    | []            => []
    | (cons y ys)   => 
        match (eqDec x y) with 
        | left _    => remove v e x ys
        | right _   => cons y (remove v e x ys)
        end
    end.  

Arguments remove {v} {e}.

Lemma remove_still : forall (v:Type) (e:Eq v) (x y:v) (xs:list v),
    x <> y -> y :: xs -> y :: (remove x xs).
Proof.
    intros v e x y. induction xs as [|a xs IH].
    - intros _ H. inversion H.
    - intros Exy H. simpl. destruct (eqDec x a) eqn:Exa. 
        + apply IH.
            { assumption. }
            { destruct H as [H1|H2]. 
                { exfalso. apply Exy. rewrite <- H1. assumption. }
                { assumption. }
            }
        + destruct H.  
            { left. assumption. }
            { right. apply IH; assumption. }
Qed.


Lemma remove_mon : forall (v:Type) (e:Eq v) (x:v) (xs ys:list v),
    xs <= ys -> (remove x xs) <= (remove x ys).
Proof.
    intros v e x. induction xs as [|a xs IH]; simpl; intros ys H.
    - intros y Hy. inversion Hy.
    - destruct (eqDec x a) eqn:E.
        + apply IH. intros y Hy. apply H. right. assumption.
        + intros y Hy. destruct (eqDec y a) as [H1|H2].
            { apply remove_still. 
                { rewrite H1. assumption. }
                { apply H. left. symmetry. assumption. }
            }
            { apply IH.
                { intros z Hz. apply H. right. assumption. }
                { destruct Hy as [G1|G2].
                    { exfalso. apply H2. symmetry. assumption. }
                    { assumption. }
                 }
            }
Qed.

Lemma remove_map_incl:forall(v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(x:v)(xs:list v),
    remove (f x) (map f xs) <= map f (remove x xs).
Proof.
    intros v w e e' f x xs. induction xs as [|a xs IH]; simpl.
    - apply incl_refl.
    - destruct (eqDec x a) as [P|P].
        + destruct (eqDec (f x) (f a)) as [Q|Q].
            { assumption. }
            { exfalso. apply Q. rewrite P. reflexivity. }
        + destruct (eqDec (f x) (f a)) as [Q|Q].
            { apply incl_tl. assumption. }
            { simpl. intros y Hy. destruct Hy.
                { left. assumption. }
                { right. apply IH. assumption. }}
Qed.

Lemma remove_x_gone: forall (v:Type) (e:Eq v) (x:v) (xs:list v),
    ~ x :: remove x xs.
Proof.
    intros v e x. induction xs as [|a xs IH]; simpl.
    - intros H. assumption.
    - destruct (eqDec x a) as [Hp|Hp].
        + subst. assumption.
        + intros [H'|H'].
            { subst. apply Hp. reflexivity. }
            { apply IH. assumption. }
Qed.


Lemma remove_x_not_in : forall (v:Type) (e:Eq v) (x:v) (xs:list v),
    ~ x :: xs -> remove x xs = xs.
Proof.
    intros v e x xs. induction xs as [|a xs IH]; simpl; intros H.
    - reflexivity.
    - destruct (eqDec x a) as [Hx|Hx].
        + exfalso. apply H. left. symmetry. assumption.
        + rewrite IH.
            { reflexivity. }
            { intros H'. apply H. right. assumption. }
Qed.

Lemma remove_map : forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(x:v)(xs:list v),
    (forall (y:v), x <> y -> y :: xs -> f x <> f y) ->
    remove (f x) (map f xs) = map f (remove x xs).
Proof.
   intros v w e e' f x xs H. 
   induction xs as [|a xs IH]; simpl. 
   - reflexivity.
   - destruct (eqDec (f x) (f a)) as [Hq|Hq].
        + subst. destruct (eqDec x a) as [Hp|Hp].
            { subst. apply IH. intros y H1 H2. apply H.
                { assumption. }
                { right. assumption. }}
            { exfalso. apply H with a. 
                { assumption. }
                { left. reflexivity. }
                { assumption. }}
        + destruct (eqDec x a) as [Hp|Hp].
            { subst. exfalso. apply Hq. reflexivity. }
            { simpl. rewrite IH.
                { reflexivity. }
                { intros y H1 H2. apply H.
                    { assumption. }
                    { right. assumption. }}}
Qed.


Lemma remove_inj : forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(x:v)(xs:list v),
    x :: xs -> 
    injective_on xs f -> 
    remove (f x) (map f xs) = map f (remove x xs).
Proof.
    intros v w e e' f x xs H1 H2. apply remove_map.
    intros y H3 H4 H5. apply H3, H2; assumption.
Qed.

Lemma remove_inj2 : forall (v w:Type)(e:Eq v)(e':Eq w)(f:v -> w)(x:v)(xs:list v),
    injective_on (x :: xs) f -> 
    remove (f x) (map f xs) = map f (remove x xs).
Proof.
    intros v w e e' f x xs H1. apply remove_map.
    intros y H2 H3 H4. apply H2, H1.
    - left. reflexivity.
    - right. assumption.
    - assumption.
Qed.

Lemma remove_incl : forall (v:Type) (e:Eq v) (x:v) (xs:list v), 
    remove x xs <= xs. 
Proof.
    intros v e x xs. induction xs as [|a xs IH]; simpl.
    - apply incl_refl.
    - destruct (eqDec x a) as [H|H].
        + apply incl_tl. assumption.
        + apply incl_cons_compat. assumption.
Qed.


Lemma remove_charac : forall (v:Type) (e:Eq v) (x:v) (xs:list v),
    forall (z:v), z :: remove x xs <-> z :: xs /\ x <> z.
Proof.
    intros v e x. induction xs as [|y ys IH]; simpl; intros z.
    - split; intros H.
        + exfalso. assumption.
        + destruct H as [H _]. assumption.
    - split; intros H; destruct (eqDec x y) as [E|E].
        + subst. apply IH in H. split.
            { right. destruct H as [H _]. assumption. }
            { destruct H as [_ H]. assumption. }
        + split; destruct H as [H|H].
            { left. assumption. }
            { apply IH in H. destruct H as [H1 H2]. right. assumption. }
            { subst. assumption. }
            { apply IH in H. destruct H as [_ H]. assumption. }
        + subst. destruct H as [H1 H2]. destruct H1 as [H1|H1].
            { exfalso. apply H2. assumption. }
            { apply IH. split; assumption. }
        + simpl. destruct H as [H1 H2]. destruct H1 as [H1|H1].
            { subst. left. reflexivity. }
            { right. apply IH. split; assumption. }
Qed.

Lemma remove_diff : forall (v:Type) (e:Eq v) (x:v) (xs:list v),
    remove x xs = xs \\ [x].
Proof.
    intros v e x. induction xs as [|y ys IH].
    - reflexivity.
    - simpl. destruct (eqDec x y) as [H|H].
        + apply IH.
        + rewrite IH. reflexivity.
Qed.
