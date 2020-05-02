Inductive Dec (p:Prop) : Type :=
| isTrue : p  -> Dec p
| isFalse: ~p -> Dec p
.

Arguments isTrue {p}.
Arguments isFalse {p}.

Class Decidable (p:Prop) := { dec : Dec p }.
 
Definition check (p:Prop) (d:Decidable p) : bool :=
    if dec then true else false.

Arguments check _ {d}.

Instance decTrue   : Decidable True   := { dec := isTrue I  }.
Instance decFalse  : Decidable False  := { dec := isFalse (fun x => x) }.

Definition L1 : check True = true.
Proof. reflexivity. Qed.

Definition L2 : check False = false.
Proof. reflexivity. Qed.

Instance decImp (p q:Prop) (d1:Decidable p) (d2:Decidable q) : Decidable (p -> q)
    := { dec := 
            match dec with
            | isTrue y  => isTrue (fun _ => y)
            | isFalse y =>
                match dec with
                | isTrue x  => isFalse (fun f => y (f x))
                | isFalse x => isTrue  (fun z => match x z with end)
                end
            end
}.  

Definition L3 : check (~True) = false.
Proof. reflexivity. Qed.

Definition L4 : check (~False) = true.
Proof. reflexivity. Qed.

Definition L5 : check (True -> True) = true.
Proof. reflexivity. Qed.

Definition L6 : check (False -> True) = true.
Proof. reflexivity. Qed.

Instance decAnd (p q:Prop) (d1:Decidable p) (d2:Decidable q) : Decidable (p /\ q)
    := { dec :=
            match dec with
            | isTrue x  =>
                match dec with
                | isTrue y  => isTrue (conj x y)
                | isFalse y => isFalse 
                    (fun (H:p /\ q) =>
                        match H with
                        | conj _ y' => y y'
                        end)
                end
            | isFalse x => isFalse
                (fun (H:p /\ q) =>
                    match H with
                    | conj x' _ => x x'
                    end)
            end
}.

Definition L8 : check (True /\ True) = true.
Proof. reflexivity. Qed.


Definition L9 : check (True /\ False) = false.
Proof. reflexivity. Qed.


Definition L10 : check (False /\ True) = false.
Proof. reflexivity. Qed.


Definition L11 : check (False /\ False) = false.
Proof. reflexivity. Qed.

Instance decOr (p q:Prop) (d1:Decidable p) (d2:Decidable q) : Decidable (p \/ q)
    := { dec :=
            match dec with
            | isTrue x  => isTrue (or_introl x)
            | isFalse x =>
                match dec with
                | isTrue y  => isTrue (or_intror y)
                | isFalse y => isFalse
                    (fun (H:p \/q) =>
                        match H with
                        | or_introl x'  => x x'
                        | or_intror y'  => y y'
                        end)
                end
            end
}.

Definition L12 : check (True \/ True) = true.
Proof. reflexivity. Qed.

Definition L13 : check (True \/ False) = true.
Proof. reflexivity. Qed.

Definition L14 : check (False \/ True) = true.
Proof. reflexivity. Qed.

Definition L15 : check (False \/ False) = false.
Proof. reflexivity. Qed.

(*
Instance decEqNat (m n:nat) : Decidable (m = n) := { dec :=
    match eq_nat_dec m n with
    | left H    => _
    | right H   => _
    end

Show.
*)

(*
Compute check (False -> False) _.
Compute check (False -> True) _.
Compute check (True -> True) _.
Compute check (True -> False) _.
Compute check ((True -> False) -> False) _.

Definition as_true (c:Prop) (d:Decidable c) : Prop :=
    if dec then True else False.

Arguments as_true _ {d}.

Definition of_as_true (c:Prop) (d:Decidable c) (q:as_true c) : c.
Proof.
    unfold as_true in q. destruct dec as [H|H].
    - exact H.
    - contradiction.
Defined.

Print of_as_true.


Definition of_as_true2 (c:Prop) (d:Decidable c) (q:as_true c) : c :=
    match dec as d return (if d then True else False) -> c with
    | isTrue H  => fun _ => H
    | isFalse H => fun x => False_ind c x
    end q.

*)


