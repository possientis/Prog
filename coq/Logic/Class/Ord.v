Require Import Logic.Class.Eq.

Class Ord (a:Type) :=
  { leq      : a -> a -> Prop
  ; leqDec   : forall (x y:a), { leq x y } + { ~ leq x y }
  ; leqRefl  : forall (x:a), leq x x
  ; leqTrans : forall (x y z:a), leq x y -> leq y z -> leq x z
  ; leqAsym  : forall (x y:a), leq x y -> leq y x -> x = y
  ; leqTotal : forall (x y:a), leq x y \/ leq y x
  }.  

(* An instance of the Ord class has decidable equality                          *)
Lemma eqDec (a:Type) (o:Ord a) : forall (x y:a), { x = y } + { x <> y }.
Proof.
    intros x y. 
    destruct (leqDec x y) as [H1|H1]; 
    destruct (leqDec y x) as [H2|H2].
    - left. apply leqAsym; assumption.
    - right. intros H. apply H2. rewrite H. apply leqRefl.
    - right. intros H. apply H1. rewrite H. apply leqRefl.
    - exfalso. destruct (leqTotal x y) as [H3|H3].
        + apply H1. assumption.
        + apply H2. assumption.
Defined.

Arguments eqDec {a} {o}.

(* An instance of the Ord class can be made an instance of the Eq class         *)
Instance eqOrd (a:Type) (o:Ord a) : Eq a := { eqDec := eqDec }.

