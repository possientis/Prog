(def person {:username "john"
             :password "xxx"
             :age 34})

; keyword can be used as a function:

; with one parameter
(println (:username person))            ; "john

; with two paramters (second param is return value on failure)
(println (:nosuchkey person "Nil"))     ; "Nil"
(println (:nosuchkey person))           ; nil
(println (:nosuchkey person :notfound)) ; :notfound


; you can also use symbols in hash maps for keys
(def expense {'name "john"
              'date "2009-10-23"
              'amount 23.45}) 

(println (expense 'name))               ; "john"  
(println ('name expense))               ; "john"
(println ('nosuchkey expense))          ; nil
(println ('nosuchkey expense :notfound)); :notfound


; hash maps are also functions (of their keys and extra optional argument)
(println (person :nosuchkey :notfound)) ; :notfound
; and so are vectors (of item index)
(def names ["kyle" "zak" "rob"])
(println (names 1))                     ; "zak", indexing starts from 0
;(println (names 10))                   ; throws exception
;(println (names 10 :notfound))         ; throws exception

