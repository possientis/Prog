(define-module (bitcoin foreign)
  #:export
    ( %foreign-int-ptr
      %foreign-bottle-ptr
    )
)

(use-modules (system foreign))

(define libforeign (dynamic-link "libforeign"))

(define %foreign-int-ptr (dynamic-pointer "foreign_int" libforeign))
(define %foreign-bottle-ptr (dynamic-pointer "foreign_bottle" libforeign))


