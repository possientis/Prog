(use-modules (system foreign))

;;; names defined in (system foreign)
;;; these names can be used to describe C types in FFI
;;; The symbol '* can be used to refer to pointer types.
(display void)(newline)     ; 0
(display float)(newline)    ; 1
(display double)(newline)   ; 2
(display uint8)(newline)    ; 3
(display int8)(newline)     ; 4
(display uint16)(newline)   ; 5
(display int16)(newline)    ; 6
(display uint32)(newline)   ; 7
(display int32)(newline)    ; 8
(display uint64)(newline)   ; 9
(display int64)(newline)    ; 10

;;; platform specific
(display (eq? int int32))(newline)            ; #t for x86-64
(display (eq? unsigned-int uint32))(newline)  ; #t for x86-64
(display (eq? long int64))(newline)           ; #t for x86-64
(display (eq? unsigned-long uint64))(newline) ; #t for x86-64
(display (eq? size_t uint64))(newline)        ; #t for x86-64
(display (eq? ssize_t int64))(newline)        ; #t for x86-64
(display (eq? ptrdiff_t int64))(newline)      ; #t for x86-64

(define x 100)
(define x-as-ptr (scm->pointer x))
(display x-as-ptr)(newline)
(display (pointer? x-as-ptr))(newline)
(display (null-pointer? x-as-ptr))(newline)
(define y (pointer->scm x-as-ptr))
(display y)(newline)  ; 100
(set! y 200)
(display x)(newline)  ; 100
(display y)(newline)  ; 200

(define s "hello")
(define s-as-ptr (string->pointer s))
(display s-as-ptr)(newline)
(define s-as-bytes (pointer->bytevector s-as-ptr 6))
(display s-as-bytes)(newline)   ; #vu8(104 101 108 108 111 0) 
(define t (pointer->string s-as-ptr))
(display t)(newline)
(display (eq? s t))(newline)    ; #f



