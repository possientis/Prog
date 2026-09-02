Fail Inductive set : Type :=
| SEmpty : set
| SPair  : set -> set -> set
| SUnion : set -> set 
| SPower : set -> set
| SComp  : set -> (set -> Prop) -> set  (* good try but no *)
.
