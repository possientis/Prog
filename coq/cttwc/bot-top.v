Inductive Bot : Prop :=.   (* no constructor *)


(* Standard statement for botElim.                                              *)
Definition botElim : forall (a:Type), Bot -> a :=
    fun (a:Type) (x:Bot) => match x with end.

(* However, this one is more in line with eliminators of other types.           *)
Definition botElim2 : forall (p:Bot -> Type) , forall (x:Bot), p x :=
    fun (p:Bot -> Type) (x:Bot) => match x with end.

(* You can get botElim from botElim2.                                           *)
Definition botElim3 : forall (a:Type), Bot -> a :=
    fun (a:Type) (x:Bot) => botElim2 (fun _ => a) x.

(* You can get botElim2 from botElim.                                           *)
Definition botElim4 : forall (p:Bot -> Type), forall (x:Bot), p x :=
    fun (p:Bot -> Type) (x:Bot) => botElim (p x) x.

Inductive Top : Prop := I.

Definition topElim : forall (p:Top -> Type), p I -> forall (x:Top), p x :=
    fun (p:Top -> Type) (q:p I) (x:Top) =>
        match x with
        | I     => q
        end.
Definition L1 : forall (x:Top), x = I := topElim (fun x => x = I) (eq_refl I).

Definition L2 : forall (p:Top -> Prop) (x:Top), p x <-> p I.
refine (
    fun (p:Top -> Prop) (x:Top) => conj
        (match x as x' return p x' -> p I with I => fun x => x end)
        (fun (H:p I) => match x with I => H end)
).
Qed.

(* elim restriction: if a match analyses a proof, it must return a proof        *)
(* two exceptions to the 'elim restriction':                                    *)
(* 1. Inductive propositions and inductive predicates with no proof constructor *)
(* 2. inductive propositions and inductive predicates with a single proof cons, *)
(*    provided every non-parametric argument of the proof constructor is a proof*)

(* Bot is exempted from the elim restriction, as it has no constructor          *)

Definition L3 (x:Bot) : nat := match x with _ => 3 end.

(* Elimination of an inductive object of sort Prop                              *)
(* is not allowed on a predicate in sort Set                                    *)
(* because proofs can be eliminated only to build proofs.                       *)
Fail Definition L4 (A B:Prop) (x:A \/ B) : nat := 
    match x with 
    | or_introl _   => 3
    | or_intror _   => 5
    end.

