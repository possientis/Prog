Require Import List.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.ToList.
Require Import Core.ElemIncl.
Require Import Core.Extensionality.



Fixpoint P (xs:set) : set :=
    match xs with
    | Nil       => { Nil }
    | Cons x xs => fromList (toList (P xs) ++ map (Cons x) (toList (P xs)))
    end.

(* looks like we need decidable (::)                                            *)
(*
Lemma Powerset_charac : forall (xs z:set), z :: P xs <-> z <== xs.
Proof.
    induction xs as [|x _ xs IH].
    - admit.
    - intros z. simpl. split.
        + intros H. apply toListElem in H. rewrite toListFromList in H.
          destruct H as [z' [H1 [H2 H3]]]. apply in_app_or in H1.
          destruct H1 as [H1|H1]; apply elemIncl; intros y Hy.
            { apply consElem. right.
              apply elemIncl with z.
                { apply IH. apply toListElem. exists z'. split.
                    { assumption. }
                    { split; assumption. }}
                { assumption. }}
            { rewrite in_map_iff in H1. destruct H1 as [z0 [H1 H4]].
              apply consElem. assert (y :: z') as E.
                { apply elemIncl with z; assumption. }
              rewrite <- H1 in E. apply consElem in E. destruct E as [E|E].
                { left. assumption. }
                { right. apply elemIncl with z0.
                    { apply IH. apply toListElem. exists z0. split.
                        { assumption. }
                        { split; apply incl_refl. }}
                    { assumption. }}} 
        + intros H.


Show.
*)
