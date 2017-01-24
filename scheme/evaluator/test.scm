(load "main.scm")

(define mode 'lazy)
(define load-proc 
  (eval 
    (string->symbol 
      (string-append (symbol->string mode) "-load"))))

; more readable
(define eval-proc 
  (cond ((eq? 'strict mode) strict-eval)
        ((eq? 'analyze mode) analyze-eval)
        ((eq? 'lazy mode) lazy-eval)
        (else "error: unknown evaluation mode" mode)))

(define (do-load filename)
  (apply load-proc (list filename)))

(define (do-run expr)
  (apply eval-proc (list expr)))


(do-load "primitive.scm")           ; interpreter running file
(do-load "primitive-procedure.scm") ; interpreter running file
(do-load "environment.scm")         ; interpreter running file

(do-run                             ; interpreter running code
  '(define (setup-environment)
     (let ((initial-env
             (((environment) 'extended)
              (primitive-procedure-names)
              (primitive-procedure-objects))))
       initial-env)))


(do-run '(define base-env (environment)))

(do-run '(define extend-proc (base-env 'extended)))

(do-run '(define proc-names (primitive-procedure-names)))

(do-run '(define proc-objects (primitive-procedure-objects)))

(do-run '(display extend-proc))

(newline)
(newline)
(do-run '(display proc-names))

(newline)
(newline)
(do-run '(display proc-objects))

(newline)
(newline)
(do-run '(extend-proc proc-names proc-objects))


(exit 0)
