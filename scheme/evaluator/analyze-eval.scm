;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-analyze-eval)) 
  (begin
    (define included-analyze-eval #f)
    (display "loading analyze-eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (analyze exp)
;  (newline)(display "analyze running ...")(newline)
  (cond ((self-evaluating? exp) (analyze-self-evaluating exp))                
        ((variable? exp)        (analyze-variable exp))
        ((quoted? exp)          (analyze-quoted exp))                
        ((assignment? exp)      (analyze-assignment exp))          
        ((definition? exp)      (analyze-definition exp))           
        ((is-defined? exp)      (analyze-defined? exp))
        ((if? exp)              (analyze-if exp))                           
        ((not? exp)             (analyze-not exp))
        ((begin? exp)           (analyze-begin exp))
        ((lambda? exp)          (analyze-lambda exp))
        ((cond? exp)            (analyze-cond exp))        
        ((or? exp)              (analyze-or exp))
        ((and? exp)             (analyze-and exp))
        ((let? exp)             (analyze-let exp))
        ((named-let? exp)       (analyze-named-let exp))
        ((let*? exp)            (analyze-let* exp))
        ((letrec? exp)          (analyze-letrec exp))
        ((dorun? exp)           (analyze-dorun exp))
        ((define-syntax? exp)   (analyze-define-syntax exp))
        ((application? exp)     (analyze-application exp))   
        (else  (error "Unknown expression type -- ANALYSE" exp))))

(define (analyze-eval exp . arg)
  (let ((env (if (null? arg) global-env (car arg))))
    ((analyze exp) env)))

))  ; include guard
