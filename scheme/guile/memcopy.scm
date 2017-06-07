(define-module (guile-secp256k1)
;               #:use-module (system foreign)
               #:export (memcpy))

(use-modules (rnrs bytevectors) 
             (system foreign))


(define memcpy 
  (let ((this (dynamic-link)))
    (pointer->procedure '*
                        (dynamic-func "memcpy" this)
                        (list '* '* size_t))))


(define src-bits
  (u8-list->bytevector '(0 1 2 3 4 5 6 7)))

(define src
  (bytevector->pointer src-bits))

(define dest
  (bytevector->pointer (make-bytevector 16 0)))

(memcpy dest src 8)

(newline)
(display (pointer->bytevector dest 16))(newline)  ; #vu8(0 1 2 3 4 5 6 7 0 0 0 0 0 0 0 0)

(define test
  (let ((this (dynamic-link "libsecp256k1")))
    (dynamic-func "secp256k1_context_create" this)))

(define create
  (let ((this (dynamic-link "libsecp256k1")))
    (pointer->procedure '*
                        (dynamic-func "secp256k1_context_create" this)
                        (list int))))

(define %verify 257)
(define %sign 513)
(define %none 1)

(define p1 (create %verify)) 
(define p2 (create %sign)) 
(define p3 (create %none)) 

(display p1)(newline)
(display p2)(newline)
(display p2)(newline)






  
