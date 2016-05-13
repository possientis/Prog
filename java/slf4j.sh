#!/bin/sh

# no binding
#javac -cp /usr/share/java/slf4j-api.jar SLF4JExample.java
#java -cp .:/usr/share/java/slf4j-api.jar SLF4JExample

# SLF4J: Failed to load class "org.slf4j.impl.StaticLoggerBinder".
# SLF4J: Defaulting to no-operation (NOP) logger implementation
# SLF4J: See http://www.slf4j.org/codes.html#StaticLoggerBinder for further details.



# simple binding
javac -cp /usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-simple.jar \
  SLF4JExample.java
java -cp .:/usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-simple.jar \
  SLF4JExample

# [main] INFO SLF4JExample - Hello World


# jdk
#javac -cp /usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-jdk14.jar \
#  SLF4JExample.java
#java -cp .:/usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-jdk14.jar \
#  SLF4JExample

# May 13, 2016 5:06:48 PM SLF4JExample main
# INFO: Hello World

# NOP
#javac -cp /usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-nop.jar \
#  SLF4JExample.java
#java -cp .:/usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-nop.jar \
#  SLF4JExample


