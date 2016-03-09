; we need a hierarchy of membership statuses in our domain

(derive ::bronze ::basic)
(derive ::silver ::basic)
(derive ::gold ::premier)
(derive ::platinum ::premier)


(println (isa? ::platinum ::premier)) ; true
(println (isa? ::premier ::platinum)) ; false
(println (isa? ::xxx ::yyy))          ; false
(println (isa? ::bronze ::premier))   ; false


