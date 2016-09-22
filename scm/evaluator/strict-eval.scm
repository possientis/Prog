;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-strict-eval)) 
  (begin
    (define included-strict-eval #f)
    (display "loading strict-eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (strict-eval exp . arg)
;  (newline)(display "strict eval running ...")(newline)
  (let ((env (if (null? arg) global-env (car arg))))
    (cond ((self-evaluating? exp) (strict-eval-self-evaluating exp env))   
          ((variable? exp)        (strict-eval-variable exp env))
          ((quoted? exp)          (strict-eval-quoted exp env))                 
          ((assignment? exp)      (strict-eval-assignment exp env))           
          ((definition? exp)      (strict-eval-definition exp env))           
          ((is-defined? exp)      (strict-eval-defined? exp env))
          ((if? exp)              (strict-eval-if exp env))           
          ((not? exp)             (strict-eval-not exp env))
          ((begin? exp)           (strict-eval-begin exp env)) 
          ((lambda? exp)          (strict-eval-lambda exp env))
          ((cond? exp)            (strict-eval-cond exp env))             
          ((or? exp)              (strict-eval-or exp env))
          ((and? exp)             (strict-eval-and exp env))
          ((let? exp)             (strict-eval-let exp env))
          ((named-let? exp)       (strict-eval-named-let exp env))
          ((let*? exp)            (strict-eval-let* exp env))
          ((letrec? exp)          (strict-eval-letrec exp env))
          ((application? exp)     (strict-eval-application exp env))
          (else  (error "Unknown expression type -- STRICT-EVAL" exp)))))

))  ; include guard.
