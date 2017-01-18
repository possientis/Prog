#!/usr/bin/scm

(load "main.scm")

(define filename (caddr (program-arguments)))

(lazy-load filename)

(exit 0)

