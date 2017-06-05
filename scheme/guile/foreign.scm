(use-modules (system foreign))


(display int8)(newline)   ; 4
(display uint8)(newline)  ; 4
(display uint16)(newline) ; 5
(display double)(newline) ; 2
(display int)(newline)    ; 8
(display unsigned-int)(newline) ; 7
(display long)(newline)   ; 10
(display size_t)(newline) ; 9
(display void)(newline)   ; 0

(define mylib (dynamic-link "libsecp256k1"))

(define ptr (dynamic-pointer "secp256k1_context_create" mylib))

(display "ptr = ")(display ptr)(newline)
(display (pointer-address ptr))(newline)

(define qtr (make-pointer (pointer-address ptr)))
(display "qtr = ")(display qtr)(newline)

(display (pointer? ptr))(newline)           ;  #t
(display (pointer? %null-pointer))(newline) ; #t

(display (null-pointer? ptr))(newline)      ; #f
(display (null-pointer? %null-pointer))(newline)  ; #t

(define rtr (scm->pointer "abcdef"))
(display "rtr = ")(display rtr)(newline)

(define str (pointer->scm rtr))

(display str)(newline) 

(define bytes (pointer->bytevector rtr 32))

(display bytes)(newline)




