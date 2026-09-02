Require Import List.

Definition eq_dec (A:Type) :=
  forall x y:A, {x = y} + {x <> y}.

Lemma nat_dec : eq_dec nat.
Proof.
  unfold eq_dec. intros x. elim x.
  clear x. intro y. elim y.
  clear y. auto.
  clear y. intros. right. auto.
  clear x. intros n IH m. elim m.
  clear m. intros. right. auto.
  clear m. intros m H. clear H.
  elim (IH m).
  intro H. rewrite H. left. reflexivity.
  intro H. right. intro H'. apply H. injection H'. auto.
Qed.




(* returns the number of occurences of n in l *)
Fixpoint count (l:list nat)(n: nat) :nat :=
  match l with
    | nil     =>  0
    | (m::l') =>  match nat_dec n m with
                    | left  _ => S (count l' n)
                    | right _ => count l' n
                  end
  end.


Eval compute in (count (1::2::1::3::nil) 1).



                
