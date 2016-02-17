; clojure strings are java String
; hence useful to know the Java api

; syntax for calling java method has initial '.'

(println (.split "clojure-in-action" "-"))
(println (for [x (.split "clojure-in-action" "-")] x))

(println (.endsWith "program.clj" ".clj"))
