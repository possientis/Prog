(def a-ref (ref 0))

(println @a-ref)  ; 0

(dosync
  (ref-set a-ref 1))

(println @a-ref)  ; 1

(defmacro sync-set [r v]  ; defining macro
  (list 'dosync
        (list 'ref-set r v)))

(sync-set a-ref 2)        ; calling macro

(println @a-ref)  ; 2

(defn exhibits-oddity1 [x]
  (if (odd? x)
    (println "Very odd!"))) 

(exhibits-oddity1 23) ; Very odd!

(defn unless1 [test then]   ; 'then' will always get evaluated regardless of 'test'
  (if (not test)            ; so implementing 'unless' as function will not work
    then))                  ; due to strict evaluation of arguments

(defn exhibits-oddity2 [x]
  (unless1  (even? x)
            (println "Very odd, indeed!")))

(exhibits-oddity2 23) ; Very odd, indeed! 
(exhibits-oddity2 10) ; Very odd, indeed! ----> problem 

(defn unless2 [test then-thunk]
  (if (not test)
    (then-thunk)))  ; executing thunk only if condition 'test' not true

(defn exhibits-oddity3 [x]
  (unless2 (even? x)
           #(println "Rather odd!"))) ; #(body) -> (fn [] body)

(exhibits-oddity3 23) ; Rather odd!
(exhibits-oddity3 10) ; no message -----> it is working, BUT.. syntactic oddity '#'

; THE MACRO SOLUTION TO BY-PASS STRICT EVALUATION

(defmacro unless [test then]
  (list 'if (list 'not test)
        then))

(defn exhibits-oddity [x]
  (unless (even? x)
          (println "This is nicely odd!"))) 

(exhibits-oddity 23)  ; This is nicely odd!
(exhibits-oddity 10)  ; no message -----> it is working, with no syntactic quirks

(println  ; macroexpand is a function
  (macroexpand '(unless (even? x) (println "This is nicely odd!"))))

; (if (not unless-cond) unless-exp)
(println (macroexpand '(unless unless-cond unless-exp))) 
(println (macroexpand-1 '(unless unless-cond unless-exp))) 

; macroexpand-1 does not further expand expression
;(if (not a) (unless b do-this))
(println (macroexpand-1 '(unless a (unless b do-this))))

; macroexpand keep expanding first item of s-expression
;(if (not a) (unless b do-this))
(println (macroexpand '(unless a (unless b do-this))))


(defmacro unless-1 [test then]
 (list 'unless-2 test then)) 

(defmacro unless-2 [test then]
  (list 'if (list 'not test) then))

;(unless-2 unless-cond unless-exp)
(println (macroexpand-1 '(unless-1 unless-cond unless-exp)))

;(if (not unless-cond) unless-exp)
(println (macroexpand '(unless-1 unless-cond unless-exp)))

; the backquote starts a template
; backquote = 'syntax quote character'
; however, you need to 'unquote' certain symbol using '~'
(defmacro unless-3 [test then]
  `(if (not ~test) ~then))          ; backquote (normal quote won't do)


(defn exhibits-oddity4 [x]
  (unless-3 (even? x)
          (println "This is nicely odd!!!!"))) 

(exhibits-oddity4 23)
(exhibits-oddity4 10)

(println (quote qwerty))
(println 'qwerty)                   ; qwerty (normal quote)
(println `qwerty)                   ; user/qwerty (backquote)

(defmacro unless-4 [test & exprs]
  `(if (not ~test) (do ~exprs)))    ; this won't work ... (do (item1 item2)) you want (do item1 item2)

(defmacro unless-5 [test & exprs]
  `(if (not ~test) (do ~@exprs)))   ; unquote splice reader macro '~@'

(defn exhibits-oddity5 [x]
  (unless-5 (even? x)
            (println "This is odd!!")
            (println "This is very odd!")
            (println "This is very very odd!")))

(exhibits-oddity5 23)               ; working fine now
(exhibits-oddity5 10)               ; no message








