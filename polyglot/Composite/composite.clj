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
    [(this [data]
       (let [dictionary {}] ; dictionary is empty
         (fn [m]
          (let [operation (dictionary m :notfound)]
           (if (= operation :notfound)
             (throw (Exception. (format "Environment: unknown operation %s" m))) 
             (operation data))))))]
    ;
    ; returning no argument constructor
    ;
    (fn [] (this :ignored))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                            Expression class                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def Expression ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :eval         exp-eval
                          :apply        exp-apply
                          :to-string    to-string
                          :composite?   composite?
                          :int?         int?
                          :this         _this}]
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               (throw (Exception. (format "Expression: unknown operation %s" m)))
               (operation data))))))
     ;
     ; implementation of public interface
     ;
     (exp-eval [data]
       (fn [env] 
         (throw (Exception. "Expression::eval is not implemented"))))
     ;
     (exp-apply [data]
       (fn [args] 
         (throw (Exception. "Expression::apply is not implemented"))))
     ;
     (to-string [data]
       (throw (Exception. "Expression::to-string is not implemented")))
     ;
     (composite? [data]
       (throw (Exception. "Expression::composite? is not implemented")))
     ;
     (int? [data] false)  ; overriden by class ExpInt
     ;
     (_this [data] (data :this))]
     ;
     ; returning constructor which expects handle to concrete object as argument
     ;
    (fn [self] (this {:this self}))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                          ExpressionLeaf class                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def ExpressionLeaf ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :eval         exp-eval
                          :apply        exp-apply
                          :to-string    to-string
                          :composite?   composite?}]
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               ((data :base) m) ; delegating to base object
               (operation data))))))
     ;
     ; implementation of public interface
     ;
     (exp-eval [data]
       (fn [env] 
         (throw (Exception. "ExpressionLeaf::eval is not implemented"))))
     ;
     (exp-apply [data]
       (fn [args] 
         (throw (Exception. "ExpressionLeaf::apply is not implemented"))))
     ;
     (to-string [data]
       (throw (Exception. "ExpressionLeaf::to-string is not implemented")))
     ;
     (composite? [data] false)] ; override
     ;
     ; returning constructor which expects handle to concrete object as argument
     ;
     ; base object (wrapped in object data) has reference to concrete object
    (fn [self] (this {:base (Expression self)}))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                      ExpressionComposite class                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def ExpressionComposite  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :eval         exp-eval
                          :apply        exp-apply
                          :to-string    to-string
                          :composite?   composite?
                          ; new members
                          :nil?         exp-nil?
                          :fold-left    fold-left
                          :fold-right   fold-right
                          :eval-list    eval-list}]
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               ((data :base) m) ; delegating to base object
               (operation data))))))
     ;
     ; implementation of public interface
     ;
     (exp-eval [data]
       (fn [env] 
         (throw (Exception. "ExpressionComposite::eval is not implemented"))))
     ;
     (exp-apply [data]
       (fn [args] 
         (throw (Exception. "ExpressionComposite::apply is not implemented"))))
     ;
     (to-string [data]
       (throw (Exception. "ExpressionComposite::to-string is not implemented")))
     ;
     (composite? [data] true) ; override
     ;
     (exp-nil? [data]
       (throw (Exception. "ExpressionComposite::nil? is not implemented")))
     ;
     (fold-left [data]
       (fn [init operator] init)) ; TBI
     ;
     (fold-right [data]
       (fn [init operator] init)) ; TBI
     ;
     (eval-list [data]
       (fn [env] (ExpressionComposite nil)))]  ; TBI
    ;
    ; returning constructor which expects handle to concrete object as argument
    ;
    ; base object (wrapped in object data) has reference to concrete object
    (fn [self] (this {:base (Expression self)}))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Nil class                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def Nil  ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :eval         exp-eval
                          :apply        exp-apply
                          :to-string    to-string
                          :nil?         exp-nil?}]
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               ((data :base) m) ; delegating to base object
               (operation data))))))
     ;
     ; implementation of public interface
     ;
     (exp-eval [data]         ; override
       (fn [env] ((data :base) :this))) ; self-evaluating
     ;
     (exp-apply [data]        ; override 
       (fn [args] (throw (Exception. "Nil is not an operator"))))
     ;
     (to-string [data] "Nil") ; override
     ;
     (exp-nil? [data] true)]  ; override
     ;
    ;
    ; returning no argument constructor
    ;
    (fn [] (let [base (ref nil)     ; mutable place-holder for base object
                 data {:base base}  ; creating object data
                 self (this data)]  ; creating object
             ; adding base object (holding reference to 'self') to data
             (dosync (ref-set base (ExpressionComposite self)))
            self))))                ; returning object


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Cons class                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def Cons   ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :eval         exp-eval
                          :apply        exp-apply
                          :to-string    to-string
                          :nil?         exp-nil?
                          ; new members
                          :head         head
                          :tail         tail}]
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               ((data :base) m) ; delegating to base object
               (operation data))))))
     ;
     ; implementation of public interface
     ;
     (exp-eval [data]         ; override
       (fn [env]
         (let [values   (((data :base) :eval-list) env)
               operator (values :head)
               args     (values :tail)]
           ((operator :apply) args))))
     ;
     (exp-apply [data]        ; override 
       (fn [args] 
         (throw (Exception. "Lambda expressions are not yet supported")))) 
     ;
     (to-string [data]
       (letfn [(operator [string expr]
                 (str string (expr :to-string) " "))]
         (str (((data :base) :fold-left) "(" operator) "\b)")))
     ;
     (exp-nil? [data] false)  ; override
     ;
     (head [data] (data :head))
     ;
     (tail [data] (data :tail))]
    ;
    ; returning two arguments constructor
    ;
    (fn [car cdr] (let [base (ref nil)      ; mutable place-holder for base object
                        data {:base base :head car :tail cdr}; creating object data
                        self (this data)]       ; creating object
             ; adding base object (holding reference to 'self') to data
             (dosync (ref-set base (ExpressionComposite self)))
            self))))                ; returning object

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              ExpInt class                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def ExpInt ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :eval         exp-eval
                          :apply        exp-apply
                          :to-string    to-string
                          :int?         int?
                          ; new member
                          :to-int       to-int}]
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               ((data :base) m) ; delegating to base object
               (operation data))))))
     ;
     ; implementation of public interface
     ;
     (exp-eval [data]     ; override 
       (fn [env] ((data :base) :this)))   ; self-evaluating
     ;
     (exp-apply [data]
       (fn [args] 
         (throw (Exception. "An integer is not an operator"))))
     ;  
     (int? [data] true)   ; override
     ;
     (to-int [data] (data :value))
     ;
     (to-string [data] (str (data :value)))]
     ;
     ; returning one argument constructor
     ;
    (fn [value] (let [base (ref nil)      ; mutable place-holder for base object
                      data {:base base :value value}  ; creating object data
                      self (this data)]               ; creating object
             ; adding base object (holding reference to 'self') to data
             (dosync (ref-set base (ExpressionLeaf self)))
            self))))                                ; returning object


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              Primitive class                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def Primitive ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :eval         exp-eval
                          :apply        exp-apply
                          :to-string    to-string}]
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               ((data :base) m) ; delegating to base object
               (operation data))))))
     ;
     ; implementation of public interface
     ;
     (exp-eval [data]
       (fn [env] 
         (throw (Exception. "Primitive::eval is not implemented"))))
     ;
     (exp-apply [data]
       (fn [args] 
         (throw (Exception. "Primitive::apply is not implemented"))))
     ;
     (to-string [data]
       (throw (Exception. "Primitive::to-string is not implemented")))]
     ;
     ; returning constructor which expects handle to concrete object as argument
     ;
     ; base object (wrapped in object data) has reference to concrete object
    (fn [self] (this {:base (ExpressionLeaf self)}))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                Plus class                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def Plus   ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :eval         exp-eval
                          :apply        exp-apply
                          :to-string    to-string}]
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               ((data :base) m) ; delegating to base object
               (operation data))))))
     ;
     ; implementation of public interface
     ;
     (exp-eval [data]     ; override 
       (fn [env] ((data :base) :this)))   ; self-evaluating
     ;
     (exp-apply [data]
       (fn [args] 
         (let [operator 
               (fn [res expr]
                 (if (expr :int?)
                   (+ res (expr :to-int))
                   (throw 
                     (Exception. 
                       (format 
                         "+: argument is not a valid integer: %s"
                         (expr :to-string))))))]
           (ExpInt ((args :fold-left) 0 operator)))))
     ;  
     (to-string [data] "+")]
     ;
     ; returning no argument constructor
     ;
    (fn [] (let [base (ref nil)       ; mutable place-holder for base object
                 data {:base base}    ; creating object data
                 self (this data)]    ; creating object
             ; adding base object (holding reference to 'self') to data
             (dosync (ref-set base (Primitive self)))
            self))))                  ; returning object

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                Mult class                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def Mult   ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (let [dictionary { :eval         exp-eval
                          :apply        exp-apply
                          :to-string    to-string}]
         (fn [m]
           (let [operation (dictionary m :notfound)]
             (if (= operation :notfound)
               ((data :base) m) ; delegating to base object
               (operation data))))))
     ;
     ; implementation of public interface
     ;
     (exp-eval [data]     ; override 
       (fn [env] ((data :base) :this)))   ; self-evaluating
     ;
     (exp-apply [data]
       (fn [args] 
         (let [operator 
               (fn [res expr]
                 (if (expr :int?)
                   (* res (expr :to-int))
                   (throw 
                     (Exception. 
                       (format 
                         "*: argument is not a valid integer: %s"
                         (expr :to-string))))))]
           (ExpInt ((args :fold-left) 1 operator)))))
     ;  
     (to-string [data] "*")]
     ;
     ; returning no argument constructor
     ;
    (fn [] (let [base (ref nil)       ; mutable place-holder for base object
                 data {:base base}    ; creating object data
                 self (this data)]    ; creating object
             ; adding base object (holding reference to 'self') to data
             (dosync (ref-set base (Primitive self)))
            self))))                  ; returning object







(def x (Nil))
(println ((x :this) :to-string))
(println (x :int?))
(println (x :composite?))
(println (x :nil?))
(println (x :to-string))
(println (((x :eval) false) :to-string))

(def y (Cons (ExpInt 42) (Nil)))
(println ((y :head) :to-string))
(println ((y :tail) :to-string))
(def z (Mult))
(println (z :to-string))
    












