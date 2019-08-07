



allLengths : List String -> List Nat
allLengths []       = []
allLengths (w :: ws) = length w :: allLengths ws

