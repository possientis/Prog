{-# LANGUAGE LambdaCase #-}

dayOfTheWeek :: Int -> String
dayOfTheWeek 0 = "Sunday"
dayOfTheWeek 1 = "Monday"
dayOfTheWeek 2 = "Tuesday"
dayOfTheWeek 3 = "Wednesday"
dayOfTheWeek 4 = "Thursday"
dayOfTheWeek 5 = "Friday"
dayOfTheWeek 6 = "Saturday"


dayOfTheWeek' :: Int -> String
dayOfTheWeek' i = case i of
    0 ->    "Sunday"
    1 ->    "Monday"
    2 ->    "Tuesday"
    3 ->    "Wednesday"
    4 ->    "Thursday"
    5 ->    "Friday"
    6 ->    "Saturday"

{- LANGUAGE LambdaCase -}
dayOfTheWeek'' :: Int -> String
dayOfTheWeek'' = \case
    0 ->    "Sunday"
    1 ->    "Monday"
    2 ->    "Tuesday"
    3 ->    "Wednesday"
    4 ->    "Thursday"
    5 ->    "Friday"
    6 ->    "Saturday"


