Require Import Arith.
Require Import List.


Fixpoint nochange (n:nat) (l:list nat) : list nat :=
  match n with 
    | 0         => match l with
                    | nil     => nil
                    | x::l' => x::l'
                   end
    | S p       => match l with 
                    | nil     => nil
                    | x::l' => x:: (nochange p l')
                  end
   end.

Lemma example1: forall (n:nat)(l: list nat),
  nochange n l = l.
Proof.
  intro n. elim n. simpl. intro l. elim l; auto.

  clear n. intros n IH l. unfold nochange. fold nochange.
  elim l. auto. clear l. intros a l H. clear H. rewrite IH. auto.
Qed.


Lemma example2: forall (n:nat)(l:list nat),
  nochange n l = nochange (S n) l.
Proof.
  intros n. elim n. intro l. elim l. simpl. auto. intros.
  unfold nochange. 
  
