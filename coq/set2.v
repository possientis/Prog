Require Import set.

Fixpoint subset2_n (n:nat) : set -> set -> Prop :=
  match n with 
    | 0   => (fun _ _     => True)
    | S p => (fun a b     =>
      match a with
        | Empty           => True
        | Singleton x     => 
          match b with
            | Empty       => False
            | Singleton y => subset2_n p x y /\ subset2_n p y x
            | Union y z   => subset2_n p (Singleton x) y \/
                             subset2_n p (Singleton x) z 
          end
        | Union x y       => subset2_n p x b /\ subset2_n p y b
      end)
  end.

Lemma subset_bool_prop : forall (n:nat)(a b:set),
  subset2_n n a b <-> subset_n n a b = true.
Proof. 
(* induction on n *)
  intro n. elim n. 
  (* n = 0 *)
  intros a b. simpl. tauto.
  (* n -> n+1 *) (* induction on a *)
  clear n. intros n IH. intro a. elim a.
  (* a = Empty *)
  intro b. simpl. tauto.
  (* a = Singleton x *)(* induction on b *)
  clear a. intros x IH'. intro b. elim b.
  (* b = Empty *)
  simpl. split. apply False_ind. intro H. discriminate H. 
  (* b = Singleton y *)
  clear b. intros y IH''. simpl. split. intro H. apply lemma_and.
  apply IH. tauto. apply IH. tauto.
  intro H. split. 
  apply IH. apply lemma_and_true_l with (q:= subset_n n y x). exact H. 
  apply IH. apply lemma_and_true_r with (p:= subset_n n x y). exact H.
  (* b = Union y z *)
  clear b. intros y IHy z IHz. simpl. split. intro H.

  

