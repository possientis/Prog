#!/bin/sh
# This shell script necessary as scala 2.9.2 does not support JDK 8
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scala -deprecation $1 $2 $3



