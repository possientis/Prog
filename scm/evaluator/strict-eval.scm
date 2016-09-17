;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-strict-eval)) 
  (begin
    (define included-strict-eval #f)
    (display "loading strict-eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (strict-eval exp . arg)
;  (newline)
;  (display "---------------------> strict eval is called")
;  (newline)
  (let ((env (if (null? arg) global-env (car arg))))
    (cond ((self-evaluating? exp) (strict-eval-self-evaluating exp env))   
          ((variable? exp)        (strict-eval-variable exp env))
          ((quoted? exp)          (strict-eval-quoted exp env))                 
          ((assignment? exp)      (strict-eval-assignment exp env))           
          ((definition? exp)      (strict-eval-definition exp env))           
          ((is-defined? exp)      (eval-defined? exp env))
          ((if? exp)              (eval-if exp env))                           
          ((not? exp)             (eval-not exp env))
          ((begin? exp)           (eval-begin exp env)) 
          ((lambda? exp)          (eval-lambda exp env))
          ((cond? exp)            (eval-cond exp env))             
          ((or? exp)              (eval-or exp env))
          ((and? exp)             (eval-and exp env))
          ((let? exp)             (eval-let exp env))
          ((named-let? exp)       (eval-named-let exp env))
          ((let*? exp)            (eval-let* exp env))
          ((letrec? exp)          (eval-letrec exp env))
          ((application? exp)     (eval-application exp env))
          (else  (error "Unknown expression type -- STRICT-EVAL" exp)))))

))  ; include guard.
