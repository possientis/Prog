; Decorator Design Pattern

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Pizza                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Pizza ; constuctor
  (let ((let-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'description) (description data))
              ((eq? m 'cost)        (cost data))
              (else (error "Pizza: unknown operation " m)))))
    ;
    (define (description data)
      (error "Pizza::description is not implemented"))
    ;
    (define (cost data)
      (error "Pizza::cost is not implemented"))
    ;
    ; returning no argument constructor
    (lambda () (this 'no-data))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               PlainPizza                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define PlainPizza  ; constructor
  (let ((let-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'description) (description data)) ; override
              ((eq? m 'cost)        (cost data))        ; override
              (else ((base data) m))))) ; passing on to base object
    ;
    (define (description data) "Plain pizza")
    (define (cost data) 3.0)
    (define (base data) (cadr data))  ; data = (list 'data base)
    ;
    ; returning no argument constructor
    (lambda() (this (list 'data (Pizza))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              PizzaDecorator                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define PizzaDecorator  ; constructor
  (let ((let-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'description) (description data)) ; override
              ((eq? m 'cost)        (cost data))        ; override
              ((eq? m 'pizza)       (get-pizza data)) 
              (else ((base data) m))))) ; passing on to base object
    ;
    (define (description data) ((get-pizza data) 'description))
    (define (cost data)        ((get-pizza data) 'cost))
    (define (base data) (cadr data))  ; data = (list 'data base)
    (define (get-pizza data) (caddr data))
    ;
    ; returning one argument interface
    (lambda (pizza-object) (this (list 'data (Pizza) pizza-object)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              WithExtraCheese                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define WithExtraCheese ; constructor
  (let ((let-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'description) (description data)) ; override
              ((eq? m 'cost)        (cost data))        ; override
              (else ((base data) m))))) ; passing on to base object
    ;
    (define (description data)
      (string-append ((get-pizza data) 'description) " + extra cheese"))
    ;
    (define (cost data) (+ ((get-pizza data) 'cost) 0.5))
    (define (base data) (cadr data))  ; data = (list 'data base)
    (define (get-pizza data) ((base data) 'pizza))
    ;
    ; returning one argument interface
    (lambda(pizza-object) (this (list 'data (PizzaDecorator pizza-object))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              WithExtraOlives                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define WithExtraOlives ; constructor
  (let ((let-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'description) (description data)) ; override
              ((eq? m 'cost)        (cost data))        ; override
              (else ((base data) m))))) ; passing on to base object
    ;
    (define (description data)
      (string-append ((get-pizza data) 'description) " + extra olives"))
    ;
    (define (cost data) (+ ((get-pizza data) 'cost) 0.7))
    (define (base data) (cadr data))  ; data = (list 'data base)
    (define (get-pizza data) ((base data) 'pizza))
    ;
    ; returning one argument interface
    (lambda(pizza-object) (this (list 'data (PizzaDecorator pizza-object))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              WithExtraAnchovies                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define WithExtraAnchovies ; constructor
  (let ((let-name-encapsulation 'dont-care))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'description) (description data)) ; override
              ((eq? m 'cost)        (cost data))        ; override
              (else ((base data) m))))) ; passing on to base object
    ;
    (define (description data)
      (string-append ((get-pizza data) 'description) " + extra anchovies"))
    ;
    (define (cost data) (+ ((get-pizza data) 'cost) 0.8))
    (define (base data) (cadr data))  ; data = (list 'data base)
    (define (get-pizza data) ((base data) 'pizza))
    ;
    ; returning one argument interface
    (lambda(pizza-object) (this (list 'data (PizzaDecorator pizza-object))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                   Main                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plain-pizza (PlainPizza))

(define nice-pizza  (WithExtraCheese (PlainPizza)))

(define super-pizza (WithExtraOlives 
                    (WithExtraCheese (PlainPizza))))

(define ultra-pizza (WithExtraAnchovies 
                    (WithExtraOlives 
                    (WithExtraCheese (PlainPizza)))))

(display "Plain Pizza: ")
(display "\tCost: ")(display (plain-pizza 'cost))
(display "\tDescription: ") (display (plain-pizza 'description)) (newline)

(display "Nice Pizza: ")
(display "\tCost: ")(display (nice-pizza 'cost))
(display "\tDescription: ") (display (nice-pizza 'description)) (newline)

(display "Super Pizza: ")
(display "\tCost: ")(display (super-pizza 'cost))
(display "\tDescription: ") (display (super-pizza 'description)) (newline)

(display "Ultra Pizza: ")
(display "\tCost: ")(display (ultra-pizza 'cost))
(display "\tDescription: ") (display (ultra-pizza 'description)) (newline)

(exit 0)
