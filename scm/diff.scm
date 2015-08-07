(define (variable? x) (symbol? x))

(define (same-variable? v1 v2)
  (and (variable? v1) (variable? v2) (eq? v1 v2)))

(define (sum? e)
  (and (pair? e) (eq? (car e) '+)))

(define (addend e) (cadr e))

(define (augend e) (caddr e))

(define (product? e)
  (and (pair? e) (eq? (car e) '*)))

(define (multiplier e) (cadr e))

(define (multiplicand e) (caddr e))


(define (deriv expr var)
  (cond ((number? expr) 0)
        ((variable? expr)
         (if (same-variable? expr var) 1 0))
        ((sum? expr)
         (make-sum (deriv (addend expr) var)
                   (deriv (augend expr) var)))
        ((product? expr)
         (make-sum
           (make-product (multiplier expr)
                         (deriv (multiplicand expr) var))
           (make-product (deriv (multiplier expr) var)
                         (multiplicand expr))))
        (else (error "unkown expression type -- DERIV" expr))))

(define (=number? expr num)
  (and (number? expr) (= expr num)))

(define (make-sum e1 e2)
  (cond ((=number? e1 0) e2)
        ((=number? e2 0) e1)
        ((and (number? e1) (number? e2)) (+ e1 e2))
        (else (list '+ e1 e2))))

(define (make-product e1 e2)
  (cond ((or (=number? e1 0) (=number? e2 0)) 0)
        ((=number? e1 1) e2)
        ((=number? e2 1) e1)
        ((and (number? e1) (number? e2)) (* e1 e2))
        (else (list '* e1 e2))))
