#!/bin/sh

javac -classpath /usr/share/java/clojure-1.6.0.jar Driver.java
java -cp .:/usr/share/java/clojure-1.6.0.jar Driver
