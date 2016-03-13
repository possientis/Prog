(import '(java.util Calendar TimeZone))

(println (. (. (Calendar/getInstance) (getTimeZone)) (getDisplayName)))

; you can remove a few parantheses
(println (. (. (Calendar/getInstance) getTimeZone) getDisplayName))

; use the dotdot macro

(println (.. (Calendar/getInstance) (getTimeZone) (getDisplayName)))

; since we are not passing any argument to getTimeZone and getDisplayName
(println (.. (Calendar/getInstance) getTimeZone getDisplayName))

; if you need to pass arguments to methods, proceed as follows

(println 
  (..
    (Calendar/getInstance)
    (getTimeZone)
    (getDisplayName true TimeZone/SHORT)))


