(import
  '(java.util List ArrayList Random)
  '(java.util.concurrent))    ; you need a quote here 


; better in conjunction with namespace
(ns my-namespace 
  (:import (java.util Set)))  ; you cannot have a quote here

(println (ns-interns 'my-namespace)) ; no mention of java in there :(

(import '(java.text SimpleDateFormat)) ; 'new' below will fail unless you import 

(println (ns-interns 'my-namespace)) ; no mention of java in there :(

; instantiating java object from clojure with 'new'
(def x (new SimpleDateFormat "yyyy-MM-dd"))

; If the first symbol in a list ends with a '.', that symbol is assumed
; to be a class name, and the call is assumed to be to a constructor
; of that class.

; IDIOMATIC
(def y (SimpleDateFormat. "yyyy-MM-dd"))  ; same as before, but binding y

(println x) ; #<SimpleDateFormat java.text.SimpleDateFormat@f67a0200>
(println y) ; #<SimpleDateFormat java.text.SimpleDateFormat@f67a0200> 

(println (= x y)) ; true (guessing objects are immutable, sharing same address)

; calling instance method of java object with a new '.' macro
; (.methodName object arg1 arg2 ...)
(defn date-from-date-string [date-string]
  (let [sdf (SimpleDateFormat. "yyyy-MM-dd")]
    ; IDIOMATIC
    (.parse sdf date-string)))

(def z (date-from-date-string "2016-03-11"))
(println z)

;(ClassName/staticMethod args*)
; you can also call java static methods
; IDIOMATIC
(println (Long/parseLong "12321"))
(println (. Long parseLong "12321"))    ; see '.' operator below
(println (. Long (parseLong "12321")))  ; see '.' operator below

; accessing java static fields
; Warning: (import '(package class1 class2 ..))
; the syntax (import '(java.util.Calendar)) will fail

(import '(java.util Calendar))
(println Calendar/JANUARY)      ; 0
(println Calendar/FEBRUARY)     ; 1

; these calls allow acces to static methods 
; THE DOT OPERATOR 'in the scope of' -- mainly used for macros
; you have idiomatic equivalent syntax
; (. Classname-symbol method-symbol args*)
; (. Classname-symbol (method-symbol args*))

(println (. System getenv "PATH"))
(println (. System (getenv "PATH")))


; now the '.' operator for instance methods
; (. instance-expr method-symbol args*)
; (. instance-expr (method-symbol args*))
(println (.parse x "2016-03-11"))         ; previous syntax
(println (. x parse "2016-03-11"))        ; dot operator
(println (. x (parse "2016-03-11")))      ; dot operator

(import '(java.util Random))
(def rnd1 (Random.))
(def rnd2 (new Random)) ; same

(println (. rnd1 nextInt 10))
(println (. rnd1 (nextInt 10)))
(println (. rnd2 nextInt 10))
(println (. rnd2 (nextInt 10))) ; useful syntax when call made inside macro

; now conside
; (. Classname-symbol member-symbol)  ; access public field of a class
; (. instance-expr    member-symbol)  ; access public filed of instance of a class

(println (. Calendar DECEMBER))       ; 11

(println (System/getenv))




