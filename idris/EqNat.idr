data EqNat : (num1 : Nat) -> (num2:Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

eqS : {num1 : Nat} -> {num2 : Nat} -> (p : EqNat num1 num2) -> EqNat (S num1) (S num2)
eqS (Same num) = Same (S num)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z          = Just $ Same 0
checkEqNat Z (S k)      = Nothing 
checkEqNat (S k) Z      = Nothing
checkEqNat (S k) (S j)  = case checkEqNat k j of
  Nothing   => Nothing
  (Just p)  => Just $ eqS p






