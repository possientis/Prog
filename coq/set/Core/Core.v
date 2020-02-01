(* NEXT: ===> Incl                                                              *)

Require Import Le.
Require Import List.
Require Import Plus.
Require Import Compare_dec.

Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Order.

(* This is where it all starts: we need to define the membership, inclusion     *)
(* and equality relations on set, but we know that these relations cannot be    *)
(* defined independently of each other. The membership statement 'x :: y'       *)
(* should be equivalent to the inclusion '{x} <== y', while the equality        *)
(* 'x == y' should be equivalent to the double inclusion 'x <== y' and          *)
(* 'y <== x'. The stategy we shall adopt is to focus solely on the inclusion    *)
(* relation, providing a standalone definition without reference to set         *)
(* membership or set equality so as to avoid the complexity of mutually         *)
(* recursive definitions. However, we cannot define set inclusion directly as   *)
(* any such attempt would lead to a definition which Coq cannot regard as       *)
(* well-founded. In order to satisfy Coq with our definition, we shall define   *)
(* a sequence of inclusion relations indexed by the natural numbers.            *)
(* The key to this definition is that the relation incl_n (S n) is defined      *)
(* in terms of the relation incl_n n, so Coq has no trouble accepting this.     *)
(* Heuristically, if we ignore the distinction between the 'levels' (S n)       *)
(* and n, the following definition expresses the fact that the inclusion        *)
(* '{x}\/xs <== ys' should hold if and only if:                                 *)
(*      (i)  xs <== ys holds                                                    *)
(*      (ii) x is itself an 'element' of ys                                     *)
(* where (ii) is expressed as the existence of a set y in (the list of) ys      *)
(* which is 'equal' to x, i.e. such that the double inclusion holds.            *)

Fixpoint incl_n (n:nat) (xs ys:set) : Prop := 
    match n with 
    | 0     => True
    | S n   => 
        match xs with
        | Nil                   => True
        | Cons x xs             =>
            incl_n n xs ys    /\
            exists (y:set), 
                In y (toList ys) /\ incl_n n x y /\ incl_n n y x 
        end
    end
.

(* We were not able to define the inclusion relation directly and we defined    *)
(* instead a sequence of binary relations on the type set. The next lemma       *)
(* crucially shows that given two sets xs and ys, for n large enough all the    *)
(* statements 'incl_n n xs ys' are equivalent. This fundamental fact will allow *)
(* us to define the inclusion relation as a sort of 'pointwise' limit of our    *)
(* sequence of relations.                                                       *)
Lemma incl_n_Sn : forall (n:nat) (xs ys:set),
    order xs + order ys <= n -> (incl_n n xs ys <-> incl_n (S n) xs ys).
Proof.
    induction n as [|n IH]; intros xs ys.
    - intros H. apply le_0 in H. apply sum_0 in H. destruct H as [H1 H2].
      apply order_0 in H1. apply order_0 in H2. rewrite H1, H2. simpl.
      split; intros H; assumption.
    - intros H. remember (S n) as m eqn:E. split.
        + intros H'. destruct xs as [|x xs].
            { apply I. }
            { rewrite E in H'. simpl in H'.    
              destruct H' as [H1 [y [H2 [H3 H4]]]].
              simpl. split.
                { apply IH.
                    { apply weaken_l' with (order (Cons x xs)).
                        { rewrite E in H. assumption. }
                        { simpl. apply le_n_S. rewrite max_sym. apply n_le_max. }
                    }
                    { assumption. }
                }
                { exists y. split.
                    { assumption. }
                    { split.
                        { apply IH. 
                            { rewrite E in H.
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order ys).
                                    { assumption. }
                                    { apply orderToList. assumption. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                        { apply IH.
                            { rewrite plus_comm. rewrite E in H.
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order ys).
                                    { assumption. }
                                    { apply orderToList. assumption. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                    }
                }
            }
        + intros H'. destruct xs as [|x xs]; rewrite E.
            { apply I. } 
            { simpl in H'. destruct H' as [H1 [y [H2 [H3 H4]]]]. split.
                { apply IH. 
                    { apply weaken_l' with (order (Cons x xs)).
                        { rewrite E in H. assumption. }
                        { simpl. apply le_n_S. apply m_le_max. }
                    }
                    { assumption. }
                } 
                { exists y. split.
                    { assumption. }
                    { split.
                        { apply IH.
                            { rewrite E in H.
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order ys).
                                    { assumption. }
                                    { apply orderToList. assumption. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                        { apply IH.
                            { rewrite plus_comm. rewrite E in H.
                              apply weaken_l' with (order (Cons x xs)).
                                { apply weaken_r with (order ys).
                                    { assumption. }
                                    { apply orderToList. assumption. }
                                }
                                { simpl. apply le_n_S. apply n_le_max. }
                            }
                            { assumption. }
                        }
                    }
                }
            }
Qed.

(* Having proved the fundamental lemma incl_n_Sn, we provide a few easy         *)
(* technical results allowing us to deduce inclusion statements of the form     *)
(* 'incl_n m xs ys' from other inclusion statements involving a different       *)
(* natural number (assumed to be large enough). In the present case, provided   *)
(* n is large enough and n <= m, we can go from n to m.                         *)
Lemma incl_le_n_m : forall (xs ys:set) (n m:nat),
    order xs + order ys <= n    -> 
    n <= m                      -> 
    incl_n n xs ys              -> 
    incl_n m xs ys.
Proof.
    intros xs ys n m H1 H2. induction  H2  as [H2|m H2 IH].
    - auto.
    - intros H. apply (incl_n_Sn m).
        + apply le_trans with n; assumption.
        + apply IH. assumption.
Qed.

(* Equally, provided n is large enough and n <= m, we can go from m to n        *)
Lemma incl_le_m_n : forall (xs ys:set) (n m:nat),
    order xs + order ys <= n    -> 
    n <= m                      ->
    incl_n m xs ys              ->
    incl_n n xs ys.
Proof.
    intros xs ys n m H1 H2. induction  H2  as [H2|m H2 IH].
    - auto.
    - intros H. apply IH. apply incl_n_Sn.
        + apply le_trans with n; assumption.
        + assumption.
Qed.

(* As a consequence of the two previous lemmas, provided both n and m are large *)
(* enough we can go from n to m without making any assumption on whether n <= m.*) 
Lemma incl_n_m : forall (xs ys:set) (n m:nat),
    order xs + order ys <= n    ->
    order xs + order ys <= m    ->
    incl_n n xs ys              -> 
    incl_n m xs ys.
Proof.
    intros xs ys n m Hn Hm H. destruct (le_dec n m) as [H'|H'].
    - apply incl_le_n_m with n; assumption.
    - apply incl_le_m_n with n.
        + assumption.
        + apply not_le in H'. unfold gt in H'. unfold lt in H'.
          apply le_trans with (S m).
            { apply le_S, le_n. }
            { assumption. }
        + assumption.
Qed.

(* All inclusion statements of the form 'incl_n n Nil x' are true.              *)
Lemma incl_n_Nil : forall (x:set) (n:nat), incl_n n Nil x.
Proof. intros x n. destruct n as [|n]; apply I. Qed.

(* For n large enough, if an inclusion statement is true in relation to xs ys,  *)
(* it is still true after you add an element to ys.                             *)
Lemma incl_n_Cons : forall (xs ys y:set) (n:nat),
    order xs <= n -> incl_n n xs ys -> incl_n n xs (Cons y ys).
Proof.
    intros xs ys y n. revert xs ys y. 
    induction n as [|n IH]; intros xs ys y H1 H2. 
    - apply I.
    - destruct xs as [|x xs].
        + apply I.
        + destruct H2 as [H2 H3]. split.
            { apply IH.
                { simpl in H1. apply le_S_n in H1. 
                  apply le_trans with (max (order x) (order xs)).
                    { apply m_le_max. }
                    { assumption. }
                }
                { assumption. }
            }
            { destruct H3 as [z [H3 [H4 H5]]]. 
              exists z. split.
                { right. assumption. }
                { split; assumption. }
            }
Qed.

(* Given x, for n large enough the inclusion statement 'incl_n n x x' holds     *)
Lemma incl_n_refl : forall (x:set) (n:nat),
    order x <= n -> incl_n n x x.
Proof.
    intros x n. revert x. induction n as [|n IH]; intros x H.
    - apply I.
    - destruct x as [|x xs].
        + apply I.
        + split.
            { apply incl_n_Cons.
                { simpl in H. apply le_S_n in H.
                  apply le_trans with (max (order x) (order xs)).
                    { apply m_le_max. }
                    { assumption. }
                }
                { apply IH. 
                  simpl in H. apply le_S_n in H.
                  apply le_trans with (max (order x) (order xs)).
                    { apply m_le_max. }
                    { assumption. }
                }
            }
            { exists x. split.
                { left. reflexivity. }
                { simpl in H. apply le_S_n in H. split; apply IH;
                  apply le_trans with (max (order x) (order xs)).
                      { apply n_le_max. }
                      { assumption. }
                      { apply n_le_max. }
                      { assumption. }
                }
            }
Qed.
