roots :: Float -> Float -> Float -> (Float, Float)
roots a b c = ((-b -d)/e, (-b + d)/e) where {
  d = sqrt(b * b  - 4 * a * c);
  e = 2 * a
}

roots' :: Float -> Float -> Float -> (Float, Float)
roots' a b c = ((-b -d)/e, (-b + d)/e) where 
  d = sqrt(b * b  - 4 * a * c)
  e = 2 * a

