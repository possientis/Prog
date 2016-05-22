Definition bar (a:Type) := a->Type.
(*
Definition foo (a:Type)(b:bar a):= prod a b.
*)
Definition foo (a:Type) := prod a (bar a).
