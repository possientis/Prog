def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

def twice (α : Type) (f : α → α) (x : α) : α := f (f x)

def thrice (α : Type) (f : α → α) (x : α) : α := f ( f (f x)) 

variables (α β γ : Type)

def compose' (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

#check compose
#check compose'

#print compose
#print compose'

