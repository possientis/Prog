; Interpreter Design Pattern

; from the Gang of Four book:
; "If a particular kind of problem occurs often enough, then it might be
; worthwhile to express instances of the problem as sentences in a simple
; language. Then you can build an interpreter that solves the problem by 
; interpreting these sentences. For example, searching for strings that 
; match a pattern is a common problem. Regular expressions are a standard 
; language for specifying patterns of strings. Rather than building custom 
; algorithms to match each pattern against strings, search algorithms could 
; interpret a regular expression that specifies a set of strings to match."
;
; Each regular expression r has an associated language L(r) (which is a set
; of strings) defined by the recursion:
;
;  - r = Lit(s)        -> L(r) = {s}
;  - r = And(r1, r2)   -> L(r) = L(r1).L(r2)     (see definition of '.')
;  - r = Or(r1, r2)    -> L(r) = L(r1) U L(r2)
;  - r = Many(r1)      -> L(r) = U_k L(r1)^k     (see definition of '.')
;
;  where given A,B sets of strings the product A.B is defined as the set of 
;  strings A.B = { a ++ b | a in A, b in B }, and where it is understood that
;  A^0 = {""} and A^1 = A. 
;
; Given a regular expression r and a string s, many reasonable questions 
; can be asked in relation to r and s. When using the command 'grep', the
; question being asked is whether there exist a substring s' of s which
; belongs to the language of r. One of the first questions of interest is
; of course whether s itself belongs to L(r).

(define (assert! condition message)
  (if (not condition) (error "assert:" message)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               Virtual Table                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define virtual-table   ; constructor
  (let () ; name encapsulation
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'to-string) (to-string data))
              ((eq? m 'interpret) (interpret data))
              (else (error "virtual-table: unknown operation error" m)))))
    ;
    (define (to-string data) (cadr data))
    (define (interpret data) (caddr data))
    ;
    ; returning two argument constructor
    (lambda (to-string interpret)
      (this (list 'data to-string interpret)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                           Regular Expressions                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reg-exp ;; constructor
  (let () ; name encapsulation
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'to-string) (to-string data)) ; virtual
              ((eq? m 'interpret) (interpret data)) ; virtual
              ((eq? m 'recognize) (recognize data)) ; not virtual
              (else (error "reg-exp: unknown operation error" m)))))
    ;
    (define (to-string data)
      (let ((table (virtual-table data)))
        ((table 'to-string) (self data))))
    ;
    (define (interpret data)
      (let ((table (virtual-table data)))
        (lambda (input)
          ((table 'interpret) (self data) input))))
    ;
    (define (recognize data)
      (lambda (input) #f))  ; TODO
    ;
    (define (self data) (cadr data))
    ;
    (define (virtual-table data) (caddr data))
    ;
    ; returning two arguments constructor
    (lambda (self virtual-table)  ; passing pointer to derived object
      (this (list 'data self virtual-table)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                           Literal Expressions                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (lit-to-string self) (self 'literal))
(define (lit-interpret self input) 'TODO)

(define lit-virtual-table (virtual-table lit-to-string lit-interpret))

(define lit-exp   ; constructor
  (let ()         ; name encapsulation
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'literal) (literal data))
              (else ((base data) m))))) ; passing request to base object
    ;
    (define (literal data) (caddr data))
    (define (base data) (cadr data))
    ;
    ; returning single argument constructor
    (lambda (literal)
            ; creating object data with stub for base object
      (let ((data (list 'data 'base literal)))
        (let ((object (this data))) ; creating object from object data
        ; updating object-data with proper base object
        (set-car! (cdr data) (reg-exp object lit-virtual-table))
        object)))))  ; returning object
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Testing                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (stub-to-string self) "stub-to-string")
(define (stub-interpret self input) "stub-interpret")


(define (test-virtual-table)
  (let ((table (virtual-table stub-to-string stub-interpret)))
    (assert! (eq? (table 'to-string) stub-to-string) 
             "test-virtual-table: to-string")
    (assert! (eq? (table 'interpret) stub-interpret) 
             "test-virtual-table: interpret")
))

(define (test-reg-exp)
  (let ((table (virtual-table stub-to-string stub-interpret)))
    (let ((object (reg-exp #f table)))
      (assert! (equal? (object 'to-string) "stub-to-string")
               "test-reg-exp: to-string")
      (assert! (equal? ((object 'interpret) #f) "stub-interpret")
               "test-reg-exp: interpret")
      (assert! (eq? ((object 'recognize) #f) #f)  ; TODO
               "test-reg-exp: recognize")
)))

(define (test-lit-exp)
  (let ((lit (lit-exp "abc")))
    (assert! (equal? (lit 'literal) "abc")
             "test-lit-exp: literal")
    (assert! (equal? (lit 'to-string) "abc")
             "test-lit-exp: to-string")
))


(define (test-all)
  (test-virtual-table)
  (test-reg-exp)
  (test-lit-exp)
)

(test-all)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Main                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(exit 0)
