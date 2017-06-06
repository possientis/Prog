(define-module (libsecp256k1)
               #:use-module (system foreign)
               #:export (memcpy))

(set! %search-load-path "/usr/lib/x86_64-linux-gnu/")

(define libsecp (dynamic-link "libsecp256k1"))

(define memcpy 
  (let ((this (dynamic-link)))
    (pointer->procedure '*
                        (dynamic-func "memcpy" this)
                        (list '* '* size_t))))

(use-modules (rnrs bytevectors))

(define src-bits
  (u8-list->bytevector '(0 1 2 3 4 5 6 7)))

(define src
  (bytevector->pointer src-bits))

(define dest
  (bytevector->pointer (make-bytevector 16 0)))

(memcpy dest src 8)

(display (pointer->bytevector dest 16))(newline)  ; #vu8(0 1 2 3 4 5 6 7 0 0 0 0 0 0 0 0)





  
