#!/bin/sh
# This shell script necessary as scala 2.9.2 does not support JDK 8
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac $1 $2 $3 $4 $5
# using fsc (creates a deamon for faster further compilation) doesn't seem to improve speed
#env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 fsc $1 $2 $3 $4 $5
