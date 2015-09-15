doubleUs x y = doubleMe x + doubleMe y
doubleMe x = x + x
doubleSmallNumber x = if x > 100
                        then x
                        else x + x
conanO'Brien = "It's a-me, Conan O'Brien!"

boomBangs xs = [if x < 10 then "BOOM!" else "BANG!" | x <- xs, odd x]
