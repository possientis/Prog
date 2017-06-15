(use-modules 
  (bitcoin foreign)
  (system foreign))

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


(display %foreign-int-ptr)(newline)
(display (pointer? %foreign-int-ptr))(newline)
(display (null-pointer? %foreign-int-ptr))(newline)

(define x 456)
(define ptr1 (scm->pointer x))
(display ptr1)(newline)
(define y (pointer->scm ptr1))
(display y)(newline)  ; 456

(define bytes1 (pointer->bytevector %foreign-int-ptr 4))

(display bytes1)(newline)

(define ptr2 (bytevector->pointer bytes1)) 

(display ptr2)(newline)
(display (equal? ptr2 %foreign-int-ptr))(newline)

;;; feels like pointer->pointer *ptr must be a pointer itself
(display (dereference-pointer ptr2))(newline)

(define ptr3 (string->pointer "hello"))
(define bytes2 (pointer->bytevector ptr3 6))
(display bytes2)(newline) 
(display (pointer->string ptr3))(newline)












