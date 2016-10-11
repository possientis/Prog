#!/usr/bin/scm

(load "main.scm")

(define filename (caddr (program-arguments)))

(new-load filename)

(exit 0)

