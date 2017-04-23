(use-modules (ice-9 vlist))

(define vh0 vlist-null)
(display vh0)(newline)

(define vh1 (vhash-consq 'a 1 vh0))
(display "vh1 = ")(display vh1)(newline)

(define vh2 (vhash-consq 'b 2 vh1))
(display "vh2 = ")(display vh2)(newline)

(define vh3 (vhash-consq 'c 3 vh2))
(display "vh3 = ")(display vh3)(newline)

(display "(vhash-assq 'a vh3) = ")(display (vhash-assq 'a vh3))(newline)
(display "(vhash-assq 'b vh3) = ")(display (vhash-assq 'b vh3))(newline)
(display "(vhash-assq 'c vh3) = ")(display (vhash-assq 'c vh3))(newline)
(display "(vhash-assq 'd vh3) = ")(display (vhash-assq 'd vh3))(newline)

(display "(vlist->list vh3) = ")(display (vlist->list vh3))(newline)

(define vh4 (alist->vhash '((a . 1)(b . 2)(c . 3)) hashq))
(display "vh4 = ")(display vh4)(newline)


(define list1 
  (vlist-map (lambda (x)
               (let ((key (car x))(val (cdr x)))
                 (cons key (* val val))))
             vh4))
(display "list1= ")(display list1)(newline) ; vlist, not a vhash

(define vh5 (alist->vhash (vlist->list list1) hashq))
(display "vh5 = ")(display vh5)(newline)

(display "(vhash? vh0) = ")(display (vhash? vh0))(newline)
(display "(vhash? vh1) = ")(display (vhash? vh1))(newline)
(display "(vhash? vh2) = ")(display (vhash? vh2))(newline)
(display "(vhash? vh3) = ")(display (vhash? vh3))(newline)
(display "(vhash? vh4) = ")(display (vhash? vh4))(newline)
(display "(vhash? vh5) = ")(display (vhash? vh5))(newline)
(display "(vhash? list1) = ")(display (vhash? list1))(newline)

(display "hash  = ")(display hash)(newline)     ; for equal?
(display "hashq = ")(display hashq)(newline)    ; for eq?
(display "hashv = ")(display hashv)(newline)    ; for eqv?

(define vh6 (vhash-consq 'a 4 vh3))             ; key 'a already known
(display "vh6 = ")(display vh6)(newline)
(display "(vlist->list vh6) = ")(display (vlist->list vh6))(newline)
(display "(vhash-assq 'a vh6) = ")(display (vhash-assq 'a vh6))(newline)
(display "(vhash-assq 'a vh6) = ")(display (vhash-assq 'a vh6))(newline)

(define vh7 (vhash-delq 'a vh6))
(display "vh7 = ")(display vh7)(newline)
(display "(vlist->list vh7) = ")(display (vlist->list vh7))(newline)







