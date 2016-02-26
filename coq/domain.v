Section domain.
  Variables (D:Set) (op:D->D->D)(sym:D->D)(e:D).
  Let diff : D->D->D :=
    fun (x y:D) => op x (sym y).
End domain.
