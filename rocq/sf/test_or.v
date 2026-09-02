Definition or_comm' : forall (P Q:Prop), P \/ Q -> Q \/ P :=
    fun (P Q:Prop) =>
        fun (pq:P \/ Q) => 
            match pq with
            | or_introl p   => or_intror p
            | or_intror q   => or_introl q
            end.
