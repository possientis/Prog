Set Implicit Arguments.

Print option.
(* Inductive option (A : Type) : Type :=  
    | Some : A -> option A 
    | None : option A 
*)

Definition pred_option (n:nat) : option nat :=
  match n with
    | 0         => None
    | S p       => Some p
  end.

Eval compute in pred_option 0.
Eval compute in pred_option 345.

Definition pred2_option (n:nat) : option nat :=
  match pred_option n with 
    | None      => None
    | Some p    => pred_option p
  end.

Eval compute in pred2_option 0.
Eval compute in pred2_option 1.
Eval compute in pred2_option 2.
Eval compute in pred2_option 345.
