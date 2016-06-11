Module Type DICT.

  Parameters key data dict : Set.

  Parameter empty : dict.

  Parameter add : key -> data -> dict -> dict.

  Parameter find : key -> dict -> option data.

  Axiom empty_def : forall k:key, find k empty = None.

  Axiom success :   forall (d:dict)(k:key)(v:data), 
    find k (add k v d) = Some v.

  Axiom diff_key :  forall (d:dict)(k k':key)(v:data),
    k <>  k' -> find k (add k' v d) = find k d.

End DICT.
