#!/bin/sh

# create a symbolic link to this file called 'gradle' in /usr/local/bin

HOME=/home/john/Libs/gradle-3.2.1

env GRADLE_HOME=${HOME} ${HOME}/bin/gradle "$@"
