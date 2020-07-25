(* NEXT: ===> Order                                                             *)
(* This is the starting point of this whole project. We are interested in       *)
(* constructing a model of set theory within Coq. So we first define a type     *)
(* which will represent our universe of sets. To define  our sets we follow     *)
(* our intuition of lists: We start with the empty set 'Nil' and given two      *)
(* sets x and xs, we can add the element 'x' to the set 'xs' with a 'Cons'      *)
(* operation, so that 'Cons x xs' effectively represents {x} \/ xs. So our      *)
(* sets are effectively finite lists of sets, and in particular all our sets    *)
(* are finite. This may appear as a serious drawback for a model of set theory. *)
(* It would be a lot more interesting if the axiom of infinity did hold in our  *)
(* model. However, the hope is that a lot of interesting mathematics can still  *)
(* be done within this framework, at least from an pedagogical point of view.   *)
Inductive set : Type :=
| Nil   : set
| Cons  : set -> set -> set
.

(* A set can be viewed as a list of sets                                        *)
Fixpoint toList (x:set) : list set :=
    match x with
    | Nil           => nil
    | (Cons x xs)   => cons x (toList xs)
    end.
(* A list of set can be viewed as a set                                         *)
Fixpoint fromList (xs:list set) : set :=
    match xs with
    | nil           => Nil
    | cons x xs     => Cons x (fromList xs)
    end.

(* In fact the correspondance between sets and list of sets is a bijection      *)
Lemma fromListToList : forall (xs:set), fromList (toList xs) = xs.
Proof.
    induction xs as [|x _ xs IH].
    - reflexivity. 
    - simpl. rewrite IH. reflexivity.
Qed.

Lemma toListFromList : forall (xs:list set), toList (fromList xs) = xs.
Proof.
    induction xs as [|x xs IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.
