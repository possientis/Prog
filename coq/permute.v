Require Import List.

(* inductive predicate expressing the fact that two lists are obtained from
each other, by the permutation of two consecutive elements  *)
Inductive transposition {A:Type} : list A -> list A -> Prop :=
  | transp_pair : forall(x y:A), transposition (x::y::nil) (y::x::nil)
  | transp_gen  : forall (l m l1 l2 : list A), 
    transposition l m -> transposition (l1++l++l2) (l1++m++l2).

(* one common issue with this sort of definition is that constructors of the
inductive predicates are akin to 'axioms', and it is very easy to define the
wrong thing, or things that are inconsistent, or incomplete etc *)

(* Here is another way to go about it *)
Definition transposition' {A:Type} (l: list A) (m:list A) : Prop := 
  exists (l1 l2:list A) (x y:A), 
  l = l1++(x::y::nil)++l2 /\ m = l1++(y::x::nil)++l2.

(* just in case, this may allow use to use 'auto with transp_base' *)
Hint Resolve transp_pair transp_gen : transp_base.

(* ideally, you want to check the equivalence between the two notions *)
Lemma tranposition_check: forall (A:Type)(l m:list A),
  transposition l m <-> transposition' l m.
Proof.
  intros A l m. split. intro H. generalize H. elim H. intros. 
  unfold transposition'. exists nil, nil, x, y. auto.
  clear H l m. intros l m l1 l2 H0 H1 H2. clear H2.
  cut (transposition' l m). clear H0 H1. intro H.
  unfold transposition' in H. elim H. intro l3. clear H. intro H.
  elim H. intro l4. clear H. intro H. 
  elim H. intro x. clear H. intro H.
  elim H. intro y. clear H. intro H.
  elim H. clear H. intros H0 H1.
  unfold transposition'.
  exists (l1++l3), (l4++l2), x, y. rewrite H0, H1. clear H0 H1.
