; connector object
(define (connector)
  ; public interface
  (define (dispatch m)
    (cond ((eq? m 'set-value!) set-value!)
          ((eq? m 'forget-value!) forget-value!)
          ((eq? m 'has-value?) (has-value?))
          ((eq? m 'get-value) (get-value))
          ((eq? m 'connect!) connect!)
          (else (display "connector: unknown operation error\n"))))
  ; private members
  (define (set-value! value user)
    'ok)
  ;
  (define (forget-value! user)
    'ok)
  ;
  (define (has-value?)
    #f)
  ;
  (define (get-value)
    #f)
  ;
  (define (connect constraint)
    'ok)
  ;
  (define (inform-about-value)
    'ok)
  ;
  (define (inform-about-no-value)
    'ok)
  ; returning public interface
  dispatch)

; adder object (constraint)
(define (adder a1 a2 sum)
  'ok)


(define (multiplier a b c)
  'ok)

(define (constant const a)
  'ok)

(define (probe label a)
  'ok)
