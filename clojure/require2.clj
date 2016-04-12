; use 'require' to import clojure namespaces
; use 'import' to import java code
; use 'use' with parcimony to add stuff to your own namespace

; IT IS MORE IDIOMATIC TO USE THE 'ns' MACRO



;(println (split "name,address,city" #",")) ; unable to resolve symbol 'split'

; #"," is regex pattern, not char literal
(println (clojure.string/split "name,address,city" #",")) ; [name address city]
; this worked without require
(require 'clojure.string) ; redundant it seems

; still need full namespace/var-name syntax

(require 'clojure.string 'clojure.test)

(println (clojure.string/join " " ["name" "address" "city"])) ; name address city

(clojure.test/is (= 1 2))

(require ['clojure.string :as 'string])

(println (string/capitalize "foo")) ; Foo

(require '[clojure.string :as string]) ; syntactic sugar to avoid quote for each item inside vector

(require 'clojure.string '[clojure.test :as test])

(test/is (= 1 1))

(require '(clojure string test))      ; yet another possible syntax for multiple require

(require '(clojure [string :as string] test))

(println (string/join [1 2 3])) ; 123

(require '[clojure.string :as string] :verbose)

(require '[clojure.test :as test] :verbose)
(require '[clojure.test :as test] :verbose :reload)

(use 'clojure.string)   ; creates name conflict with clojure.core

(println (join [1 2 3])) ; 123

(use '[clojure.string :only [split]]) ; ONLY USE 'use' with :only !!!!!

(println (str (split "a,b,c" #",")))  ; ["a" "b" "c"] 

(use '[clojure.string :exclude [replace reverse]])

(use '[clojure.string :rename {replace str-replace reverse str-reverse}])

(println (str-reverse "foobar")); raboof

(println (java.util.Date.)) ; #inst "2016-04-12T13:09:54.476-00:00"

(import 'java.util.Date)    ; syntax
(import '(java.util Date))  ; yet another
(import '[java.util Date])  ; yet another

(import '(java.util Date GregorianCalendar))

(println (Date.)) ; #inst "2016-04-12T13:10:58.584-00:00"

(println Date)              ; java.util.Date
(println GregorianCalendar) ; java.util.GregorianCalendar

; YOu SHOULD USE THE 'ns' MACRO, which brings it all together
(ns my-great-project.core
  "This namespace is CRAZY!"
  (:use [clojure.string :only [split join]] :reload) ; notice the absence of ' 
  (:require clojure.stacktrace
            [clojure.test :as test]
            (clojure template walk) :verbose)
  (:import (java.util Date GregorianCalendar)))

