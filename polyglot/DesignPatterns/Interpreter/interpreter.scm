; Interpreter Design Pattern
(require 'string-search) ; substring?
(require 'srfi-1)        ; filter
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
      (lambda (input)
        (let ((result (((self data) 'interpret) input)))
          (not (eq? #f (member input result))))))
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

(define (lit-interpret self input)
  (let ((literal (self 'literal)))
    (if (eq? 0 (substring? literal input))
      (list literal)
      (list))))


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
;;                               And Expressions                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (and-to-string self)
  (let ((s1 ((self 'left) 'to-string))
        (s2 ((self 'right) 'to-string)))
    (string-append s1 s2)))

(define (and-interpret self input)
  (let ((left-list (((self 'left) 'interpret) input)))
    (apply 
      append 
      (map 
        (lambda (s1) 
          (let ((remain 
                  (substring input (string-length s1) (string-length input))))
            (let ((right-list (((self 'right) 'interpret) remain)))
              (map (lambda (s2) (string-append s1 s2)) right-list))))
        left-list))
))
    

(define and-virtual-table (virtual-table and-to-string and-interpret))

(define and-exp   ; constructor
  (let ()         ; name encapsulation
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'left) (left data))
              ((eq? m 'right) (right data))
              (else ((base data) m))))) ; passing request to base object
    ;
    (define (left data) (caddr data))
    (define (right data) (cadddr data))
    (define (base data) (cadr data))
    ;
    ; returning two arguments constructor
    (lambda (left right)
            ; creating object data with stub for base object
      (let ((data (list 'data 'base left right)))
        (let ((object (this data))) ; creating object from object data
        ; updating object-data with proper base object
        (set-car! (cdr data) (reg-exp object and-virtual-table))
        object)))))  ; returning object
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                Or Expressions                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (or-to-string self)
  (let ((s1 ((self 'left) 'to-string))
        (s2 ((self 'right) 'to-string)))
    (string-append "(" s1 "|" s2 ")")))

(define (or-interpret self input)
  (let ((left-list (((self 'left) 'interpret) input))
        (right-list (((self 'right) 'interpret) input)))
    (append left-list right-list)))

(define or-virtual-table (virtual-table or-to-string or-interpret))

(define or-exp   ; constructor
  (let ()         ; name encapsulation
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'left) (left data))
              ((eq? m 'right) (right data))
              (else ((base data) m))))) ; passing request to base object
    ;
    (define (left data) (caddr data))
    (define (right data) (cadddr data))
    (define (base data) (cadr data))
    ;
    ; returning two arguments constructor
    (lambda (left right)
            ; creating object data with stub for base object
      (let ((data (list 'data 'base left right)))
        (let ((object (this data))) ; creating object from object data
        ; updating object-data with proper base object
        (set-car! (cdr data) (reg-exp object or-virtual-table))
        object)))))  ; returning object
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              Many Expressions                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (many-to-string self)
  (let ((s ((self 'regex) 'to-string)))
    (string-append "(" s ")*")))

(define (many-interpret self input)
  (let ((raw-list (((self 'regex) 'interpret) input)))
    (let ((left-list (filter (lambda (s) (not (string-null? s))) raw-list)))
      (cons 
        ""  ; forall r:reg-exp, "" belongs to L(r*)
        (apply 
          append 
          (map 
            (lambda (s1) 
              (let ((remain 
                    (substring input (string-length s1) (string-length input))))
                (let ((right-list (many-interpret self remain)))  ; recursive call
                  (map (lambda (s2) (string-append s1 s2)) right-list))))
            left-list))))))


(define many-virtual-table (virtual-table many-to-string many-interpret))

(define many-exp  ; constructor
  (let ()         ; name encapsulation
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'regex) (regex data))
              (else ((base data) m))))) ; passing request to base object
    ;
    (define (regex data) (caddr data))
    (define (base data) (cadr data))
    ;
    ; returning single argument constructor
    (lambda (regex)
            ; creating object data with stub for base object
      (let ((data (list 'data 'base regex)))
        (let ((object (this data))) ; creating object from object data
        ; updating object-data with proper base object
        (set-car! (cdr data) (reg-exp object many-virtual-table))
        object)))))  ; returning object
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Testing                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (stub-to-string self) "stub-to-string")
(define (stub-interpret self input) (list "stub-interpret"))


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
      (assert! (equal? ((object 'interpret) "") (list "stub-interpret"))
               "test-reg-exp: interpret")
)))

(define (test-lit-exp)
  (let ((lit (lit-exp "abc")))
    (assert! (equal? (lit 'literal) "abc")              "test-lit-exp: literal")
    (assert! (equal? (lit 'to-string) "abc")            "test-lit-exp: to-string")
    (assert! (equal? ((lit 'interpret) "") ())          "test-lit-exp: interpret")
    (assert! (equal? ((lit 'interpret) "a") ())         "test-lit-exp: interpret")
    (assert! (equal? ((lit 'interpret) "ab") ())        "test-lit-exp: interpret")
    (assert! (equal? ((lit 'interpret) "abc") '("abc")) "test-lit-exp: interpret")
    (assert! (equal? ((lit 'interpret) "abcx") '("abc"))"test-lit-exp: interpret")
    (assert! (eq? ((lit 'recognize) "") #f)             "test-lit-exp: interpret")
    (assert! (eq? ((lit 'recognize) "a") #f)            "test-lit-exp: interpret")
    (assert! (eq? ((lit 'recognize) "ab") #f)           "test-lit-exp: interpret")
    (assert! (eq? ((lit 'recognize) "abc") #t)          "test-lit-exp: interpret")
    (assert! (eq? ((lit 'recognize) "abcx") #f)         "test-lit-exp: interpret")
))

(define (test-and-exp)
  (let ((l1 (lit-exp "abc"))
        (l2 (lit-exp "def")))
    (let ((a (and-exp l1 l2)))
      (assert! (eq? (a 'left) l1)                       "test-and-exp: left")
      (assert! (eq? (a 'right) l2)                      "test-and-exp: right")
      (assert! (equal? (a 'to-string) "abcdef")         "test-and-exp: to-string")
      (assert! (equal? ((a 'interpret) "") ())          "test-and-exp: interpret")
      (assert! (equal? ((a 'interpret) "a") ())         "test-and-exp: interpret")
      (assert! (equal? ((a 'interpret) "ab") ())        "test-and-exp: interpret")
      (assert! (equal? ((a 'interpret) "abc") ())       "test-and-exp: interpret")
      (assert! (equal? ((a 'interpret) "abcd") ())      "test-and-exp: interpret")
      (assert! (equal? ((a 'interpret) "abcde") ())     "test-and-exp: interpret")
      (assert! (equal? ((a 'interpret) "abcdef") '("abcdef"))    
               "test-and-exp: interpret")
      (assert! (equal? ((a 'interpret) "abcdefx") '("abcdef"))         
               "test-and-exp: interpret")
      (assert! (eq? ((a 'recognize) "") #f)             "test-and-exp: interpret")
      (assert! (eq? ((a 'recognize) "a") #f)            "test-and-exp: interpret")
      (assert! (eq? ((a 'recognize) "ab") #f)           "test-and-exp: interpret")
      (assert! (eq? ((a 'recognize) "abc") #f)          "test-and-exp: interpret")
      (assert! (eq? ((a 'recognize) "abcd") #f)         "test-and-exp: interpret")
      (assert! (eq? ((a 'recognize) "abcde") #f)        "test-and-exp: interpret")
      (assert! (eq? ((a 'recognize) "abcdef") #t)       "test-and-exp: interpret")
      (assert! (eq? ((a 'recognize) "abcdefx") #f)      "test-and-exp: interpret")
)))

(define (test-or-exp)
  (let ((l1 (lit-exp "abc"))
        (l2 (lit-exp "def")))
    (let ((o (or-exp l1 l2)))
      (assert! (eq? (o 'left) l1) "test-or-exp: left")
      (assert! (eq? (o 'right) l2) "test-or-exp: right")
      (assert! (equal? (o 'to-string) "(abc|def)") "test-or-exp: to-string")
      (assert! (equal? ((o 'interpret) "") ())          "test-or-exp: interpret")
      (assert! (equal? ((o 'interpret) "a") ())         "test-or-exp: interpret")
      (assert! (equal? ((o 'interpret) "ab") ())        "test-or-exp: interpret")
      (assert! (equal? ((o 'interpret) "abc") '("abc")) "test-or-exp: interpret")
      (assert! (equal? ((o 'interpret) "abcx")'("abc")) "test-or-exp: interpret")
      (assert! (equal? ((o 'interpret) "d") ())         "test-or-exp: interpret")
      (assert! (equal? ((o 'interpret) "de") ())        "test-or-exp: interpret")
      (assert! (equal? ((o 'interpret) "def") '("def")) "test-or-exp: interpret")
      (assert! (equal? ((o 'interpret) "defx")'("def")) "test-or-exp: interpret")
      (assert! (eq? ((o 'recognize) "") #f)             "test-or-exp: interpret")
      (assert! (eq? ((o 'recognize) "a") #f)            "test-or-exp: interpret")
      (assert! (eq? ((o 'recognize) "ab") #f)           "test-or-exp: interpret")
      (assert! (eq? ((o 'recognize) "abc") #t)          "test-or-exp: interpret")
      (assert! (eq? ((o 'recognize) "abcx") #f)         "test-or-exp: interpret")
      (assert! (eq? ((o 'recognize) "d") #f)            "test-or-exp: interpret")
      (assert! (eq? ((o 'recognize) "de") #f)           "test-or-exp: interpret")
      (assert! (eq? ((o 'recognize) "def") #t)          "test-or-exp: interpret")
      (assert! (eq? ((o 'recognize) "defx") #f)         "test-or-exp: interpret")
)))

(define (test-many-exp)
  (let ((l (lit-exp "abc")))
    (let ((m (many-exp l)))
      (assert! (eq? (m 'regex) l) "test-many-exp: regex")
      (assert! (equal? (m 'to-string) "(abc)*")          "test-many-exp: to-string")
      (assert! (equal? ((m 'interpret) "") '(""))        "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret) "a") '(""))       "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret) "ab") '(""))      "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret) "abc")'("" "abc"))     
               "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret) "abca")'("" "abc"))    
               "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret)"abcab")'("" "abc"))   
               "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret)"abcabc")'("" "abc" "abcabc"))  
               "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret)"abcabca")'("" "abc" "abcabc")) 
               "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret)"abcabcab")'("" "abc" "abcabc"))
               "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret)"abcabcabc")'("" "abc" "abcabc" "abcabcabc"))
               "test-many-exp: interpret")
      (assert! (equal? ((m 'interpret)"abcabcabcx")'("" "abc" "abcabc" "abcabcabc"))
               "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "") #t)             "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "a") #f)            "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "ab") #f)           "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "abc") #t)          "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "abca") #f)         "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "abcab") #f)        "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "abcabc") #t)       "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "abcabca") #f)      "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "abcabcab") #f)     "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "abcabcabc") #t)    "test-many-exp: interpret")
      (assert! (eq? ((m 'recognize) "abcabcabcx") #f)   "test-many-exp: interpret")
)))


(define (test-all)
  (test-virtual-table)
  (test-reg-exp)
  (test-lit-exp)
  (test-and-exp)
  (test-or-exp)
  (test-many-exp)
)


;(test-all)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 Main                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define a (lit-exp "a"))
(define b (lit-exp "b"))
(define c (lit-exp "c"))

(define aa (and-exp a (many-exp a)))  ; one or more 'a'
(define bb (and-exp b (many-exp b)))  ; one or more 'b'
(define cc (and-exp c (many-exp c)))  ; one or more 'c'

(define regex (many-exp (and-exp (or-exp aa bb) cc)))
(define str "acbbccaaacccbbbbaaaaaccccc")

(display (string-append "regex = " (regex 'to-string) "\n"))
(display (string-append "string = \"" str "\"\n"))
(display "The recognized prefixes are:\n")

(define result
  (reverse
    (let loop ((i 0) (res '()))
      (if (< (string-length str) i)
        res
        (let ((test (substring str 0 i)))
          (if ((regex 'recognize) test)
            (loop (+ i 1) (cons (string-append "\"" test "\"") res))
            (loop (+ i 1) res)))))))

(define (pretty result)
  (string-append 
    "["
    (let loop ((res result)(str "")(start #t))
      (if (null? res) 
        str
        (if start
          (loop (cdr res) (string-append str (car res)) #f)
          (loop (cdr res) (string-append str ", " (car res)) #f))))
    "]"))

(display (pretty result))(newline)

(exit 0)
