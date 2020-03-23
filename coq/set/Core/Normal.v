(* TODO: check imports are really needed                                        *)

Require Import Core.Set.
Require Import Core.Leq.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Empty.
Require Import Core.Insert.
Require Import Core.ElemIncl.
Require Import Core.Decidability.
Require Import Core.Extensionality.

Fixpoint normalize (x:set) : set :=
    match x with
    | Nil           => Nil
    | (Cons x xs)   =>
        match (elem_dec x xs) with
        | left _    => normalize xs                         (*  we have x :: xs *)
        | right _   => insert (normalize x) (normalize xs)  (*  otherwise       *)
        end
    end.

(*
Lemma normalizeSame : forall (x:set), normalize x == x.
Proof.
    induction x as [|x IH1 xs IH2].
    - apply equalRefl.
    - simpl. destruct (elem_dec x xs) as [H|H]; simpl.
        + admit.
        +

Show.
*)
 
(*
Lemma normalizeEqual : forall (x y:set), normalize x = normalize y -> x == y.
Proof.
    induction x as [|x IH1 xs IH2]; intros y H.
    - admit.
    - simpl in H. destruct (elem_dec x xs) as [Hx|Hx].
        + admit.
        +

Show.
*)

(*
Lemma equalNormalize : forall (x y:set), x == y -> normalize x = normalize y.
Proof.
    induction x as [|x IH1 xs IH2]; intros y H.
    - apply equalSym in H. rewrite emptyIsNil in H. rewrite H. reflexivity.
    - simpl. destruct (elem_dec x xs) as [Hx|Hx].
        + admit.
        +


Show.
*)
(*
    - destruct y as [|y ys]; simpl.
        + rewrite emptyIsNil in H. inversion H.
        + destruct (elem_dec x xs) as [Hx|Hx].
            { destruct (elem_dec y ys) as [Hy|Hy].
                { apply IH2. apply doubleIncl. split.
                    { apply elemIncl. intros z Hz. 
                        assert (z :: Cons x xs) as H'.
                            { apply consElem. right. assumption. }
                        apply (equal_r (Cons x xs) (Cons y ys) z H) in H'. 
                        rewrite consElem in H'. destruct H' as [H'|H'].
                            { apply equal_l with y.
                                { apply equalSym. assumption. }
                                { assumption. }}
                            { assumption. }}
                    { apply elemIncl. intros z Hz. 
                        assert (z :: Cons y ys) as H'.
                            { apply consElem. right. assumption. }
                        apply (equal_r (Cons y ys) (Cons x xs) z) in H'. 
                            { rewrite consElem in H'. destruct H' as [H'|H'].
                                { apply equal_l with x.
                                    { apply equalSym. assumption. }
                                    { assumption. }}
                                { assumption. }}
                            { apply equalSym. assumption. }}}
                {

*)
