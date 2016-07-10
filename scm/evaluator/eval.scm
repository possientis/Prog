;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-eval)) 
  (begin
    (define included-eval #f)
    (display "loading eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (eval exp env)
;  (newline)(display "eval:\texp = ")(display exp)(newline)(newline)
;  (display "env = ")(display (env 'to-string))(newline)
;  (newline)(newline)(display "type ()+<Enter>")(read)(newline)(newline)
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
        (else  (error "Unknown expression type -- EVAL" exp))))

))  ; include guard.
