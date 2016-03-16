; this creates a java array (which is mutable)
(def tokens (.split "clojure.in.action" "\\."))

(println (alength tokens))  ; array length
(println (aget tokens 0))   ; array element get
(println (aget tokens 1))   ; array element get
(println (aget tokens 2))   ; array element get

; java array is mutable
(aset tokens 2 "actionable"); array element set
(println (aget tokens 2))   ; actionable

; other clojure functions allowing to work with java arrays
; to-array
; to-array-2d
; into-array
; make-array
; amap
; areduce

; however, use clojure data structures in preference
; to java arrays
