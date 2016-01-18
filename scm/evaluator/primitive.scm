(define (primitive-procedure? procedure) (symbol? procedure))

(define (apply-primitive-procedure procedure arguments)
  (cond ((eq? procedure '+) (add arguments))
        ((eq? procedure '*) (mul arguments))
        ((eq? procedure 'eval) (apply-eval arguments))
        (else (error "Unknown primitive procedure -- APPLY" procedure))))

(define (add arguments)
  (if (null? arguments) 0
    (+ (car arguments) (add (cdr arguments)))))

(define (mul arguments)
  (if (null? arguments) 1
    (* (car arguments) (mul (cdr arguments)))))

(define (apply-eval arguments)
  (let ((exp (car arguments)) (env (cadr arguments)) (rest (cddr arguments)))
    (if (null? rest)  ; which is expected
      (eval exp env)
      (error "Too many arguments in primitive procedure eval" arguments))))
