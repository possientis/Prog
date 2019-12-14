(* NEXT: ===> Rank                                                              *) 


Require Import List.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Empty.
Require Import Core.ToList.
Require Import Core.ElemIncl.
Require Import Core.Intersection.
Require Import Core.Decidability. 
Require Import Core.Extensionality.


(* We now define the 'power set' P xs of a set xs, i.e. the set of all subsets  *)
(* of xs. This definition is done with pattern matching on xs. If xs is the     *)
(* empty set, then it has one unique subset, namely the empty set itself. If xs *)
(* is the union xs = {x} \/ xs', then all subsets of xs are obtained by taking  *)
(* all subsets of xs', and adding to this collection all subsets of xs' with x  *)
(* as an extra element. We are not claiming that this informal description or   *)
(* indeed the formal definition below are clearly correct. However, the lemma   *)
(* following this definition will confirm its correctness.                      *)
Fixpoint P (xs:set) : set :=
    match xs with
    | Nil       => { Nil }
    | Cons x xs => fromList (toList (P xs) ++ map (Cons x) (toList (P xs)))
    end.

(* The property which characterizes our power set is what we were hoping for.   *)
(* z is an element of P xs if and only if z is a subset of xs.                  *)
Lemma powerset_charac : forall (xs z:set), z :: P xs <-> z <== xs.
Proof.
    induction xs as [|x _ xs IH].
    - intros z. split; simpl; intros H. 
        + apply consElem in H. destruct H as [H|H].
            { apply doubleIncl in H. destruct H as [H1 H2]. assumption. }
            { exfalso. apply emptyCharac in H. assumption. }
        + apply consElem. left. apply doubleIncl. split.
            { assumption. }
            { apply inclNil. }
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
        + intros H. destruct (elem_dec x z) as [H'|H'].
            { remember (z /\ xs) as z' eqn:E. assert (z' <== xs) as Z.
                { apply elemIncl. intros u H1. rewrite E in H1.
                  apply inter_charac in H1. destruct H1 as [H1 H2]. assumption. }
              apply (IH z') in Z. apply toListElem in Z.
              destruct Z as [y [H1 [H2 H3]]]. apply toListElem. 
              exists (Cons x y). split.
                { rewrite toListFromList. apply in_or_app. right.
                  apply in_map_iff. exists y. split.
                    { reflexivity. }
                    { assumption. }}
                { split.
                    { apply elemIncl. intros u H4. apply consElem.
                      assert (u :: Cons x xs) as H5.
                        { apply (elemIncl z (Cons x xs)); assumption. }
                      apply consElem in H5. destruct H5 as [H5|H5].
                        { left. assumption. }
                        { right. assert (u :: z') as H6.
                            { rewrite E. apply inter_charac. split; assumption. }
                          apply (elemIncl z' y); assumption. }}
                    { apply elemIncl. intros u H4. apply consElem in H4.
                      destruct H4 as [H4|H4].
                        { apply equal_l with x.
                            { apply equal_sym. assumption. }
                            { assumption. }}
                        { assert (u :: z') as H5.
                            { apply (elemIncl y z'); assumption. }
                          rewrite E in H5. apply inter_charac in H5.
                          destruct H5 as [H5 H6]. assumption. }}}}
            { assert (z <== xs) as H1.
                { apply elemIncl. intros u H2. assert (u :: Cons x xs) as H3.
                    { apply (elemIncl z (Cons x xs)); assumption. }
                  apply consElem in H3. destruct H3 as [H3|H3].
                    { exfalso. apply H'. apply equal_l with u; assumption. }
                    { assumption. }}
              apply IH in H1. apply toListElem in H1. 
              destruct H1 as [y [H1 H2]]. apply toListElem. exists y. split.
                { rewrite toListFromList. apply in_or_app. left. assumption. }
                { assumption. }}
Qed.

(* The power set axiom is satisfied in our model. For all x, there exists a y,  *)
(* such that for all z, z belongs to y if and only if z is a subset of x.       *)
(* In other words, for all x, the power set P x exists.                         *)
Theorem powerset : forall (x:set), exists (y:set), forall (z:set),
    z :: y <-> z <== x.
Proof.
    intros x. exists (P x). apply powerset_charac.
Qed.
