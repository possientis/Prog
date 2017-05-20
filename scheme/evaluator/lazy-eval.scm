;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-eval)) 
  (begin
    (define included-lazy-eval #f)
    (display "loading lazy-eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (lazy-eval exp . arg)
  (let ((env (if (null? arg) global-env (car arg))))
    (cond ((self-evaluating? exp) (lazy-eval-self-evaluating exp env))
          ((variable? exp)        (lazy-eval-variable exp env))
          ((quoted? exp)          (lazy-eval-quoted exp env))                 
          ((assignment? exp)      (lazy-eval-assignment exp env))           
          ((definition? exp)      (lazy-eval-definition exp env))           
          ((is-defined? exp)      (lazy-eval-defined? exp env))
          ((if? exp)              (lazy-eval-if exp env))
          ((not? exp)             (lazy-eval-not exp env))
          ((begin? exp)           (lazy-eval-begin exp env)) 
          ((lambda? exp)          (lazy-eval-lambda exp env))
          ((cond? exp)            (lazy-eval-cond exp env))             
          ((or? exp)              (lazy-eval-or exp env))
          ((and? exp)             (lazy-eval-and exp env))
          ((let? exp)             (lazy-eval-let exp env))
          ((named-let? exp)       (lazy-eval-named-let exp env))
          ((let*? exp)            (lazy-eval-let* exp env))
          ((letrec? exp)          (lazy-eval-letrec exp env))
          ((dorun? exp)           (lazy-eval-dorun exp env))
          ((define-syntax? exp)   (lazy-eval-define-syntax exp env))
          ((application? exp)     (lazy-eval-application exp env))
          (else  (error "Unknown expression type -- LAZY-EVAL" exp)))))

))  ; include guard.
