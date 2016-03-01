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
;;                      A note on this Scheme implementation                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; It is very easy to emulate duck typing in Scheme. When faced with a hierarchy
; of classes and virtual methods, we can usually get away without implementing 
; virtual tables: each object is essentially a dictionary which contains a
; reference to a base object. If a method call fails (the key is not in the
; dictionary) then the call is passed on to the base object. Method overriding
; is naturally implemented by defining a new (key value) pair in the dictionary,
; rather than letting the base object handle the call.
;
; However, there are cases of polymorphism when a base method relies on virtual
; methods, such as fold-left, fold-right and eval-list of the class 
; ExpressionComposite below. In this case, it is impossible to implement such
; base method solely on the basis of the base object data. Such implementation 
; require knowledge of the concrete object data, which is where the virtual
; table normally comes in handy.
;
; The following code was succesfully implemented in JavaScript where the object
; model seems to be what we have just described (dictionaries with a __prot__ 
; reference leading to a base object) and seemingly no virtual table under
; the hood. Why is it working in JavaScript without any notion of virtual 
; table? The answer lies in the availability of the 'this' pointer
; which seems to refer to a concrete object, even when appearing in the body
; of code belonging to a base object.
;
; We have tried to replicate this model here, by making a 'this' object
; available in the object interface, and making sure 'this' referred to
; the concrete object. So we can make it all work without virtual tables.


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
              ((eq? m 'this)        (_this data)) 
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
    (define (_this data) (cadr data))  ; data is list ('data this)
    ;
    ; returning constructor which expects handle to concrete object as argument
    ;
    (lambda (self) 
      (this (list 'data self)))))

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
              ((eq? m 'this)        ((base data) 'this))
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
    (define (base data) (cadr data))  ; data is list ('data base)
    ;
    ; returning constructor which expects handle to concrete object as argument
    ;
    ; base object (wrapped in object data) has reference to concrete object
    (lambda (self) (this (list 'data (Expression self)))))) 


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
              ((eq? m 'this)        (_this data))
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
    (define (base data) (cadr data))  ; data is list ('data base)
    ;
    (define (_this data) ((base data) 'this))
    ;
    (define (nil? data)
      (error "ExpressionComposite::nil? is not implemented"))
    ;
    (define (foldl data)
      (lambda (init operator)
        (let loop ((out init) (next (_this data)))
          (if (next 'nil?)
            out
            ; else
            (loop (operator out (next 'head)) (next 'tail))))))
    ;
    (define (foldr data)
      (lambda (init operator)
        (let ((self (_this data)))  ; concrete object
          (if (self 'nil?)
            init
            ; else
            (operator (self 'head) (((self 'tail) 'fold-right) init operator))))))
    ;
    (define (eval-list data)
      (lambda (env)
       ((foldr data) (Nil) (lambda (expr _list)
                              (Comp ((expr 'eval) env) _list)))))

    ;
    ; returning constructor which expects handle to concrete object as argument
    ;
    ; base object (wrapped in object data) has reference to concrete object
    (lambda (self) (this (list 'data (Expression self)))))) 

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
              ((eq? m 'this)        (_this data))
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
      (lambda (env) (_this data))) ; self-evaluating 
    ;
    (define (exp-apply data)
      (lambda (args) (error "Nil is not an operator")))
    ;
    (define (to-string data) "Nil")
    ;
    (define (composite? data) #t) ; override
    ;
    (define (base data) (cadr data))  ; data is list ('data base)
    ;
    (define (nil? data) #t)
    ;
    (define (_this data) ((base data) 'this))
    ;
    ; returning no argument constructor
    ;
    (lambda () (let ((data (list 'data 'base-object)))  ; creating object data
                 (let ((self (this data)))              ; creating object
                   ; adding base object (holding reference to 'self') to data
                   (set-car! (cdr data) (ExpressionComposite self))
                   self))))) ; returning object

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
              ((eq? m 'this)        (_this data))
              ;; ExpressionComposite members
              ((eq? m 'nil?)        (nil? data))
              ((eq? m 'fold-left)   ((base data) 'fold-left))   ; call base
              ((eq? m 'fold-right)  ((base data) 'fold-right))  ; call base
              ((eq? m 'eval-list)   (eval-list data))
              ;; new members
              ((eq? m 'head)        (head data))
              ((eq? m 'tail)        (tail data))
              (else (error "Comp: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data)
      (lambda (env)
        (let ((vals ((eval-list data) env)))
          (let ((operator (vals 'head)) (args (vals 'tail)))
            ((operator 'apply) args)))))
    ;
    (define (exp-apply data)
      (lambda (args) (error "Lambda expression are not yet supported")))
    ;
    (define (to-string data)
      (string-append 
        ((foldl data) "(" 
         (lambda (str expr) 
           (string-append str (expr 'to-string) " ")))
        (list->string (list #\bs)) ")")) ; backspace , control character
    ;
    (define (composite? data) #f) ; override
    ;
    (define (base data) (cadr data)); data is list ('data base car cdr)
    ;
    (define (nil? data) #f)
    ;
    (define (head data) (caddr data))
    ;
    (define (tail data) (cadddr data))
    ;
    (define (_this data) ((base data) 'this))
    ;
    (define (foldl data) ((base data) 'fold-left))
    ;
    (define (eval-list data) ((base data) 'eval-list))
    ;
    ; returning two arguments constructor
    ;
    (lambda (first rest)
      (let ((data (list 'data 'base-object first rest)))  ; creating object data
        (let ((self (this data)))                         ; creating object
          ;; adding base object (holding reference to 'self') to data
          (set-car! (cdr data) (ExpressionComposite self))
          self))))) ; returning object 

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
              ((eq? m 'this)        (_this data))
              ;; new member
              ((eq? m 'to-int)      (to-int data)) 
              (else (error "ExpInt: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data) 
      (lambda (env) (_this data)))  ;; self evaluating
    ;
    (define (exp-apply data)
      (lambda (args) (error "An integer is not an operator")))
    ;
    (define (to-string data) (number->string (caddr data))) 
    ;
    ;
    (define (base data) (cadr data))  ; data is list ('data base value)   
    ;
    (define (to-int data) (caddr data))
    ;
    (define (int? data) #t)
    ;
    (define (_this data) ((base data) 'this))
    ;
    ; returning one argument constructor 
    ;
    (lambda (value)
      (let ((data (list 'data 'base-object value))) ; creating object data
        (let ((self (this data)))                   ; creating object
          ;; adding base object (holding reference to 'self) to data
          (set-car! (cdr data) (ExpressionLeaf self))
          self))))) ; returning object


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
              ((eq? m 'this)        ((base data) 'this))
              (else (error "Primitive: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (base data) (cadr data))  ; data is list ('data base)  
    ;
    ; returning constructor which expects handle to concrete object as argument
    ;
    ; base object (wrapped in object data) has reference to concrete object
    (lambda (self) (this (list 'data (ExpressionLeaf self)))))) 

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
              ((eq? m 'this)        (_this data))
              (else (error "Plus: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data) 
      (lambda (env) (_this data)))  ;; self evaluating
    ;
    (define (exp-apply data)
      (lambda (args)
        (let ((operator (lambda (res expr)
                          (if (expr 'int?)
                            (+ res (expr 'to-int))
                            (error "+: argument is not a valid integer"
                                   (expr 'to-string))))))
          (ExpInt ((args 'fold-left) 0 operator)))))
    ;
    (define (to-string data) "+")
    ;
    (define (base data) (cadr data)) ; data is list ('data base)
    ;
    (define (_this data) ((base data) 'this))
    ;
    ; returning no argument constructor 
    ;
    (lambda ()
      (let ((data (list 'data 'base-object))) ; creating object data
        (let ((self (this data)))             ; creating object
          ;; adding base object (holding reference to 'self) to data
          (set-car! (cdr data) (Primitive self))
          self))))) ; returning object


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
              ((eq? m 'this)        (_this data))
              (else (error "Mult: unknown operation error" m)))))
    ;
    ; implementation of public interface
    ;
    (define (exp-eval data) 
      (lambda (env) (this data)))  ;; self evaluating
    ;
    (define (exp-apply data)
      (lambda (args)
        (let ((operator (lambda (res expr)
                          (if (expr 'int?)
                            (* res (expr 'to-int))
                            (error "*: argument is not a valid integer"
                                   (expr 'to-string))))))
          (ExpInt ((args 'fold-left) 1 operator)))))
    ;
    (define (to-string data) "*")
    ;
    (define (base data) data)
    ;
    (define (_this data) ((base data) 'this))
    ;
    ; returning no argument constructor 
    ;
    (lambda ()
      (let ((data (list 'data 'base-object))) ; creating object data
        (let ((self (this data)))             ; creating object
          ;; adding base object (holding reference to 'self) to data
          (set-car! (cdr data) (Primitive self))
          self))))) ; returning object

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








