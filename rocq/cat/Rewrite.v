(* Since Coq allows us to manipulate proofs as first class objects,
   it is very common to design types which not only encapsulate data,
   but also proofs that the data satisfies some required property.
   These proofs are usually deemed irrelevant, and two objects whose
   data coincide are often deemed equal, regardless of the specifics
   of the proofs attributes they contain. However, even with proof
   irrelevance, the actual mechanics of coq tactics and rewrites may 
   not be so obvious to handle, and some subtle tricks need to be 
   applied. Let us consider an example: *) 

(* Some predicate on nat *)
Parameter P : nat -> Prop.

(* Some type which encapsulate a natural number, together with a proof *)
Inductive Obj : Type :=
| make : forall n, P n -> Obj
.

(* We assume proof irrelevance *)
Axiom proof_irrelevance : forall (P:Prop) (p q:P), p = q.

(* Now let us consider the following result *)
Example obvious : forall (n m:nat) (p:P n) (q: P m),
    n = m -> make n p = make m q.
Proof.
    intros n m p q Enm. 
    Fail rewrite Enm.
    (*
    Error: Abstracting over the term "n" leads to a term
    fun n0 : nat => make n0 p = make m q
    which is ill-typed.
        Reason is: Illegal application: 
        The term "make" of type "forall n : nat, P n -> Obj"
        cannot be applied to the terms
         "n0" : "nat"
          "p" : "P n"
          The 2nd term has type "P n" which should be coercible to 
          "P n0".
   *)

   (* We simply rewrite the equality 'n = m' in the goal because the type
      of p is dependent on n. We need to abstract over p. *)
   revert p. (* same as generalize p. clear p. *)
   (* We can now successfully rewrite Enm, then re-introduce p *)
   rewrite Enm. intros p.
   (* Now both p and q are of type P m, and we simply need to use irrelevance *)
   rewrite (proof_irrelevance _ p q).
   reflexivity.
Qed.


     

