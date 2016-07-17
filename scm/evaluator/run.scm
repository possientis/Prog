#!/usr/bin/scm

(load "main.scm")

(define filename (caddr (program-arguments)))
(load-primitive filename)
(exit 0)

