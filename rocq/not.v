Check not.

(* overriding existing definition *)
Definition not (b:bool) :=
  match b with
    | true  =>  false
    | false =>  true
  end.

Check not.

(* cannot override again in same file for some reason *)
Definition not' (b:bool) := if b then false else true.

Lemma not_same : forall b:bool, not b = not' b.
Proof.
  intro b. elim b.
    clear b. simpl. reflexivity.
    clear b. simpl. reflexivity.
Qed.


Definition func1 := 
  fun (x:nat) (H:{x=0}+{x<>0}) =>
    match H with
      | left  _ => true
      | right _ => false
    end.
 
Check func1.

Definition func2 :=
  fun (x:nat) (H:{x=0}+{x<>0}) =>
    if H then true else false.

Check func2.

Lemma func_same: forall x:nat, forall H:{x=0}+{x<>0},
  func1 x H = func2 x H.
Proof.
  intros x H. elim H.
    clear H. intro H. simpl. reflexivity.
    clear H. intro H. simpl. reflexivity.
Qed.


