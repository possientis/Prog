(* NEXT: ===> Equal                                                             *) 

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.ToList.
Require Import Core.Trans.


(* We have defined the membership relation :: and the inclusion relation <==    *)
(* on sets. However, the inclusion x <== y is commonly defined in standard set  *)
(* theoretic mathematics as the implication 'z :: x -> z :: y' holding for all  *)
(* z. So the following theorem is an important vindication of our definition    *)
(* so far: any definition of membership or inclusion for which this theorem     *)
(* does not hold cannot be regarded as a 'good' definition. Note that the       *)
(* statement 'forall (z:set), z :: x -> z :: y' is likely to be a proposition   *)
(* of the 'core' language of set theory, in any reasonable conception of the    *)
(* word: it only contains set variables x, y, z, the quantification forall,     *)
(* the implication -> and the membership relation ::. By contrast, 'x <== y'    *)
(* would probably not be part of a set theoretic core language. It may be part  *)
(* of a higher level language and defined as syntactic sugar for the low level  *)
(* statement 'forall (z:set), z :: x -> z :: y'.                                *)
Theorem elemIncl : forall (x y:set), 
    x <== y <-> forall (z:set), z :: x -> z :: y.
Proof.
    intros xs ys. split.
    - intros H z Hz. 
      rewrite toListIncl in H. 
      rewrite toListElem in Hz. destruct Hz as [z' [H1 [H2 H3]]].
      apply toListElem. apply H in H1. apply toListElem in H1.
      destruct H1 as [y [H1 [H4 H5]]]. exists y. split.
      + assumption.
      + split.
        { apply inclTrans with z'; assumption. }
        { apply inclTrans with z'; assumption. }
    - intros H. apply toListIncl. intros z H'. 
      apply H.  apply toListElem. exists z. split.
      + assumption.
      + split; apply inclRefl.
Qed.

