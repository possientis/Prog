Check @conj.        (* : forall A B : Prop, A -> B -> A /\ B                    *)
Check @or_introl.   (* : forall A B : Prop, A -> A \/ B                         *) 
Check @or_intror.   (* : forall A B : Prop, B -> A \/ B                         *) 


(* Impredicative : Quantifying over Prop                                        *)

(* The following equivalences show that False, /\, \/ can be defined using      *)
(* only dependent function types.                                               *)

(* Impredicative characterization of falsity                                    *)
Definition L1 : False <-> forall (Z:Prop), Z := conj
    (fun (p:False) => match p with end)
    (fun f => f False).

(* Impredicative characterization of conjonction                                *)
Definition L2 (X Y:Prop) : X /\ Y <-> forall (Z:Prop), (X -> Y -> Z) -> Z := conj
    (fun p =>
        match p with
        | conj x y  =>
            fun Z => 
                fun f => f x y
        end)
    (fun f => conj
        (f X (fun x y => x))
        (f Y (fun x y => y))).

(* Impredicative characterization of disjunction                                *)
Definition L3 (X Y:Prop) : 
    X \/ Y <-> forall (Z:Prop), (X -> Z)->(Y -> Z)->Z := conj
        (fun (p : X \/ Y)   =>
            match p with
            | or_introl x   =>
                fun (Z:Prop)    => 
                    fun (f:X -> Z) (g:Y -> Z) => f x
            | or_intror y   =>
                fun (Z:Prop) =>
                    fun (f:X -> Z) (g:Y -> Z) => g y
            end)
        (fun (f: forall (Z:Prop), (X -> Z) -> (Y -> Z) -> Z) => 
            f (X \/ Y) (fun x => or_introl x) (fun y => or_intror y)).
            


Definition L4 : True <-> forall (Z:Prop), Z -> Z := conj
    ( fun _ => fun Z => fun z => z)
    ( fun _ => I).


Definition L5 (X Y:Set) (p:X -> Y -> Prop) : 
    (forall (x:X) (y:Y), p x y) <-> (forall (y:Y) (x:X), p x y) := conj
        (fun f => fun y => fun x => f x y)
        (fun f => fun x => fun y => f y x).

Definition L6 : forall (X Y:Set) (p:X -> Y -> Prop),
    (forall (x:X) (y:Y), p x y) <-> (forall (y:Y) (x:X), p x y) := fun X Y p => 
        conj
            (fun f => fun y => fun x => f x y)
            (fun f => fun x => fun y => f y x).

(* This tactic proof is like a proof diagram...                                 *)
Definition L7 : forall (X:Set) (p:X -> Prop), 
    ~~(forall x, p x) -> forall x, ~~p x.
Proof.
    intros X p f x g. apply f. intros f'. exact (g (f' x)).
Qed.

(* ... which can be converted as a normal proof                                 *) 
Definition L8 : forall (X:Set) (p:X -> Prop), ~~(forall x, p x) -> forall x, ~~p x 
    := fun X p f x g => f (fun f' => g (f' x)).

(* proof diagram ...                                                            *)
Definition L9 : forall (X:Set) (p:X -> Prop)(q:X -> Prop),
    (forall x, p x <-> q x) -> (forall x, q x) -> forall x, p x.
Proof.
    intros X p q f g x. destruct (f x) as [f1 f2]. exact (f2 (g x)).
Qed.


(* ... translated to normal term                                                *)
Definition L10 : forall (X:Set) (p:X -> Prop)(q:X -> Prop),
    (forall x, p x <-> q x) -> (forall x, q x) -> forall x, p x
    := fun X p q f g x => 
        match (f x) with 
        | conj _ f2 =>
            f2 (g x)
        end.

(* tactic *)
Definition L11 : forall (X:Set)(p q:X -> Prop),
    (forall x, p x /\ q x) <-> (forall x, p x) /\ (forall x, q x).
Proof.
    intros X p q. split.
    - intros f. split.
        + intros x. destruct (f x) as [f1 _]. exact f1.
        + intros x. destruct (f x) as [_ f2]. exact f2.
    - intros f x. destruct f as [f1 f2]. split.
        + exact (f1 x).
        + exact (f2 x).
Qed.

(* normal *)
Definition L12 : forall (X:Set)(p q:X -> Prop),
    (forall x, p x /\ q x) <-> (forall x, p x) /\ (forall x, q x)
    := fun X p q => conj
        (fun f => conj
            (fun x => match (f x) with conj f1 _ => f1 end)
            (fun x => match (f x) with conj _ f2 => f2 end))
        (fun f x => 
            match f with conj f1 f2 => 
                conj (f1 x) (f2 x)
            end).


Definition L13 : forall (X:Set) (Z:Prop), Z -> (forall (x:X), Z).
Proof.
    intros X Z z x. exact z.
Qed.


Definition L14 : forall (X:Set) (Z:Prop), Z -> (forall (x:X), Z) 
    := fun X Z z x => z.

Definition L15 : forall (X:Set)(p:X -> Prop)(Z:Prop),
    (forall x, p x) -> Z -> forall x, p x /\ Z.
Proof.
    intros X p Z f z x. split. 
    - exact (f x).
    - exact z.
Qed.

Definition L16 : forall (X:Set)(p:X -> Prop)(Z:Prop), 
    (forall x, p x) -> Z -> forall x, p x /\ Z 
        := fun X p Z f z x => conj (f x) z.



            
