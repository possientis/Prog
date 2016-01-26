factorial n | n < 2 = 1
factorial n         = n * factorial (n - 1)

roots :: Float -> Float -> Float -> (Float, Float)
roots a b c = ((-b -d)/e, (-b + d)/e) where {
  d = sqrt(b * b  - 4 * a * c);
  e = 2 * a
}

roots' :: Float -> Float -> Float -> (Float, Float)
roots' a b c = ((-b -d)/e, (-b + d)/e) where 
  d = sqrt(b * b  - 4 * a * c)
  e = 2 * a

