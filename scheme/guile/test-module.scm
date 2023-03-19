; the module foo/bar-module is defined in the file bar-module.scm
; This file must be located in /usr/share/guile/2.2/foo/ or else guile
; will not find it and the following 'use-modules' statement will fail

(use-modules (foo bar-module))

(frob 4)  ; frob defined in module foo/bar-module
