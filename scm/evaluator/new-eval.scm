;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-eval)) 
  (begin
    (define included-new-eval #f)
    (display "loading new-eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
(define (new-eval exp . arg)
  (let ((env (if (null? arg) global-env (car arg))))
    (let ((analyzed (analyze exp)))
      (analyzed env))))

(define (new-eval2 exp . arg)
  (let ((env (if (null? arg) global-env (car arg))))
    (cond ((self-evaluating? exp) (eval-self-evaluating exp env))                 
          ((variable? exp)        (eval-variable exp env))
          ((quoted? exp)          (eval-quoted exp env))                 
          ((assignment? exp)      (eval-assignment exp env))           
          ((definition? exp)      (eval-definition exp env))           
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
          (else  (error "Unknown expression type -- EVAL" exp)))))

))  ; include guard.
