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

(define Environment
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond (#t (error "Environment: unknown operation error" m)))))
    ; 
    ; returning no argument constructor
    ;
    (lambda () (this 'ignored))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                            Expression class                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Expression
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'eval)        (exp-eval data))
              ((eq? m 'apply)       (exp-apply data))
              ((eq? m 'to-string)   (to-string data))
              ((eq? m 'composite?)  (composite? data))
              ((eq? m 'int?)        (int? data))
              (else (error "Expression: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data)
      (lambda (env) (error "Expression::eval is not implemented")))
    ;
    (define (exp-apply data)
      (lambda (args) (error "Expression::apply is not implemented")))
    ;
    (define (to-string data)
      (error "Expression::to-string is not implemented"))
    ;
    (define (composite? data)
      (error "Expression::composite? is not implemented"))
    ;
    (define (int? data) #f)
    ;
    ; returning no argument constructor
    ;
    (lambda () (this 'ignored))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                          ExpressionLeaf class                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ExpressionLeaf
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'eval)        (exp-eval data))
              ((eq? m 'apply)       (exp-apply data))
              ((eq? m 'to-string)   (to-string data))
              ((eq? m 'composite?)  (composite? data))
              ((eq? m 'int?)        ((base data) 'int?)) ; delegating to base
              (else (error "ExpressionLeaf: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data)
      (lambda (env) (error "ExpressionLeaf::eval is not implemented")))
    ;
    (define (exp-apply data)
      (lambda (args) (error "ExpressionLeaf::apply is not implemented")))
    ;
    (define (to-string data)
      (error "ExpressionLeaf::to-string is not implemented"))
    ;
    (define (composite? data) #f) ; override
    ;
    (define (base data) data)     ; base object is only data
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (Expression))))) ; passing a base object as data


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                            ExpressionComposite class                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ExpressionComposite
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'eval)        (exp-eval data))
              ((eq? m 'apply)       (exp-apply data))
              ((eq? m 'to-string)   (to-string data))
              ((eq? m 'composite?)  (composite? data))
              ((eq? m 'int?)        ((base data) 'int?)) ; delegating to base
              ;; new members
              ((eq? m 'nil?)        (nil? data))
              ((eq? m 'fold-left)   (foldl data))
              ((eq? m 'fold-right)  (foldr data))
              ((eq? m 'eval-list)   (eval-list data))
              (else (error "ExpressionComposite: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data)
      (lambda (env) (error "ExpressionComposite::eval is not implemented")))
    ;
    (define (exp-apply data)
      (lambda (args) (error "ExpressionComposite::apply is not implemented")))
    ;
    (define (to-string data)
      (error "ExpressionComposite::to-string is not implemented"))
    ;
    (define (composite? data) #t) ; override
    ;
    (define (base data) data)     ; base object is only data
    ;
    (define (nil? data)
      (error "ExpressionComposite::nil? is not implemented"))
    ;
    (define (foldl data)
      (lambda (init operator) init))  ; TBI
    ;
    (define (foldr data)
      (lambda (init operator) init))  ; TBI
    ;
    (define (eval-list data)
      (lambda (env) (ExpressionComposite))) ; TBI
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (Expression))))) ; passing a base object as data

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                Nil class                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Nil
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'eval)        (exp-eval data))
              ((eq? m 'apply)       (exp-apply data))
              ((eq? m 'to-string)   (to-string data))
              ((eq? m 'composite?)  ((base data) 'composite?))  ; call base
              ((eq? m 'int?)        ((base data) 'int?))        ; call base
              ;; derived members
              ((eq? m 'nil?)        (nil? data))
              ((eq? m 'fold-left)   ((base data) 'fold-left))   ; call base
              ((eq? m 'fold-right)  ((base data) 'fold-right))  ; call base
              ((eq? m 'eval-list)   ((base data) 'eval-list))   ; call base
              (else (error "Nil: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data)
      (lambda (env) (this data))) ; self-evaluating 
    ;
    (define (exp-apply data)
      (lambda (args) (error "Nil is not an operator")))
    ;
    (define (to-string data) "Nil")
    ;
    (define (composite? data) #t) ; override
    ;
    (define (base data) data)     ; base object is only data
    ;
    (define (nil? data) #t)
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (ExpressionComposite))))) ; passing a base object as data

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                Comp class                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Comp  ;; cannot use 'Cons' identifier as Scheme is not case sensitive
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'eval)        (exp-eval data))
              ((eq? m 'apply)       (exp-apply data))
              ((eq? m 'to-string)   (to-string data))
              ((eq? m 'composite?)  ((base data) 'composite?))  ; call base
              ((eq? m 'int?)        ((base data) 'int?))        ; call base
              ;; ExpressionComposite members
              ((eq? m 'nil?)        (nil? data))
              ((eq? m 'fold-left)   ((base data) 'fold-left))   ; call base
              ((eq? m 'fold-right)  ((base data) 'fold-right))  ; call base
              ((eq? m 'eval-list)   ((base data) 'eval-list))   ; call base
              ;; new members
              ((eq? m 'head)        (head data))
              ((eq? m 'tail)        (tail data))
              (else (error "Comp: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data)
      (lambda (env) (this data))) ; TBI
    ;
    (define (exp-apply data)
      (lambda (args) (error "Lambda expression are not yet supported")))
    ;
    (define (to-string data) 'TBI)
    ;
    (define (composite? data) #f) ; override
    ;
    (define (base data) (car data)); data is list (base car cdr)
    ;
    (define (nil? data) #f)
    ;
    (define (head data) (cadr data))
    ;
    (define (tail data) (caddr data))
    ;
    ; returning two arguments constructor
    ;
    (lambda (first rest) (this (list (ExpressionComposite) first rest))))) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 ExpInt class                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ExpInt
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'eval)        (exp-eval data))
              ((eq? m 'apply)       (exp-apply data))
              ((eq? m 'to-string)   (to-string data))
              ((eq? m 'composite?)  ((base data) 'composite?))
              ((eq? m 'int?)        (int? data))
              ;; new member
              ((eq? m 'to-int)      (to-int data)) 
              (else (error "ExpInt: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data) 
      (lambda (env) (this data)))  ;; self evaluating
    ;
    (define (exp-apply data)
      (lambda (args) (error "An integer is not an operator")))
    ;
    (define (to-string data) (number->string (cadr data))) 
    ;
    ;
    (define (base data) (car data))     ; data is list (base value)
    ;
    (define (to-int data) (cadr data))
    ;
    (define (int? data) #t)
    ;
    ; returning one argument constructor 
    ;
    (lambda (value) (this (list (ExpressionLeaf) value)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                Primitive class                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Primitive
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'eval)        ((base data) 'eval))
              ((eq? m 'apply)       ((base data) 'apply))
              ((eq? m 'to-string)   ((base data) 'to-string))
              ((eq? m 'composite?)  ((base data) 'composite?))
              ((eq? m 'int?)        ((base data) 'int?))
              (else (error "Primitive: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (base data) data)     ; base object is only data
    ;
    ; returning no argument constructor
    ;
    (lambda () (this (ExpressionLeaf))))) ; passing a base object as data


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Plus class                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Plus
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'eval)        (exp-eval data))
              ((eq? m 'apply)       (exp-apply data))
              ((eq? m 'to-string)   (to-string data))
              ((eq? m 'composite?)  ((base data) 'composite?))
              ((eq? m 'int?)        ((base data) 'int?))
              (else (error "Plus: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data) 
      (lambda (env) (this data)))  ;; self evaluating
    ;
    (define (exp-apply data)
      (lambda (args) 'TBI))
    ;
    (define (to-string data) "+")
    ;
    (define (base data) data)
    ;
    ; returning no argument constructor 
    ;
    (lambda () (this (Primitive)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Mult class                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Mult
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'eval)        (exp-eval data))
              ((eq? m 'apply)       (exp-apply data))
              ((eq? m 'to-string)   (to-string data))
              ((eq? m 'composite?)  ((base data) 'composite?))
              ((eq? m 'int?)        ((base data) 'int?))
              (else (error "Mult: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data) 
      (lambda (env) (this data)))  ;; self evaluating
    ;
    (define (exp-apply data)
      (lambda (args) 'TBI))
    ;
    (define (to-string data) "*")
    ;
    (define (base data) data)
    ;
    ; returning no argument constructor 
    ;
    (lambda () (this (Primitive)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Main                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define env  (Environment))
(define two  (ExpInt 2))
(define seven(ExpInt 7))
(define five (ExpInt 5))
(define add  (Plus))
(define mul  (Mult))
(define exp1 (Comp add (Comp two (Comp seven (Comp five (Nil))))));(+ 2 7 5)
(define exp2 (Comp mul (Comp two (Comp exp1 (Comp five (Nil))))));(* 2 (+ 2 7 5) 5)

(display "The evaluation of the Lisp expression: ")
(display (exp2 'to-string))(newline)
(display "yields the value: ")
(display (((exp2 'eval) env) 'to-string))(newline)








