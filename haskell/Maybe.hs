data Person = Person

father :: Person -> Maybe Person
father = undefined

mother :: Person -> Maybe Person
mother = undefined

-- first option, not using the monad structure
bothGrandFathers'' :: Person -> Maybe (Person, Person)
bothGrandFathers'' p =
  case father p of
    Nothing -> Nothing
    Just f  ->
      case father f of
        Nothing -> Nothing
        Just gf ->
          case mother p of
            Nothing -> Nothing
            Just m  ->
              case father m of
                Nothing -> Nothing
                Just gm ->
                  Just (gf, gm)

-- Maybe monad without do notation 
bothGrandFathers' :: Person -> Maybe (Person, Person)
bothGrandFathers' p =
  father p >>= 
    (\f -> father f  >>= 
      (\gf -> mother p >>=
        (\m -> father m >>=
          (\gm -> return (gf, gm) ))))

bothGrandFathers :: Person -> Maybe (Person, Person)
bothGrandFathers p = do
  f   <- father p
  gf  <- father f
  m   <- mother p
  gm  <- father m
  return (gf, gm) 






