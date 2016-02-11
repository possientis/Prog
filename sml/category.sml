use "sets.sml";

datatype ('object, 'arrow) Category =
  category of ('arrow -> 'object) *
              ('arrow -> 'object) *
              ('object -> 'arrow) *
              ('arrow * 'arrow -> 'arrow)


(*
 datatype 'a SetMap = setMap of ('a Set) * ('a -> 'a) * ('a Set) 
 *)
