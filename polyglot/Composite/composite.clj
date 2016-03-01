; Composite Design Pattern

; The composite design pattern consists in creating an abstract class
; or interface 'Component' which allows client code to handle certain 
; types of primitive objects of type 'Leaf' and various combinations
; thereof in a uniform way. These combinations can be of various nature
; and are unified in a common type 'Composite', where both 'Leaf' and 
; 'Composite' are subclasses of 'Component'.
;
; There are many examples where the composite pattern is applicable
; e.g. the DOM for html and abstract syntax trees for formal languages, 
; inductive data types of Haskell and Coq, etc.
;
; In the SICP course at MIT, a key idea relating to properties of
; programming languages is the existence of 'primitive objects' (Leaf)
; and 'means of combination', allowing the creation of new objects
; (Composite) while remaining within the language. The Composite 
; patterns allows us to regard every language entity as a 'Component' 
; which can be combined with other 'Component'(either 'Leaf' or 
; 'Composite') to obtain a new Component. In Lisp we could say that 
; every Component (which we shall call 'Expression') is either a Leaf 
; (which we shall call 'ExpressionLeaf') or a list of expressions 
; (which we shall call 'ExpressionComposite'). The means of combinations 
; in this case are are simply reduced to gathering objects within lists:
;
; Expression          := ExpressionLeaf | ExpressionComposite
; ExpressionComposite := Nil | Cons Expression ExpressionComposite
;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                            Environment class                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def Environment  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data] :tbi)]))



