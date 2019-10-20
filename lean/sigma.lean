variable α : Type
variable β : α → Type

variable a : α
variable b : β a

#check sigma.mk a b
#check (sigma.mk a b).1
#check (sigma.mk a b).2
