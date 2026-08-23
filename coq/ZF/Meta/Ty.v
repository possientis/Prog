Inductive Ty : Type :=
| TySet   : Ty
| TyClass : Ty
| TyProp  : Ty
.

Inductive VarTy : Type :=
| VarTySet   : VarTy
| VarTyClass : VarTy
.

Definition toTy (vty:VarTy) : Ty :=
  match vty with
  | VarTySet   => TySet
  | VarTyClass => TyClass
  end.
