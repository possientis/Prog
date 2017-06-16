(define-module (bitcoin foreign)
  #:export
    ( %foreign-int
      %foreign-bottle-ptr
    )
)

(use-modules (system foreign) (rnrs bytevectors))

(define libforeign (dynamic-link "libforeign"))

(define %foreign-int
  (let ((ptr (dynamic-pointer "foreign_int" libforeign)))
    (let ((bytes (pointer->bytevector ptr 4)))
      (bytevector-s32-ref bytes 0 (endianness little)))))


(define %foreign-bottle-ptr (dynamic-pointer "foreign_bottle" libforeign))


