#!/bin/sh

# create a symbolic link to this file called 'gradle' in /usr/local/bin

env GRADLE_HOME=/home/john/Libs/gradle-3.2.1 \
	/home/john/Libs/gradle-3.2.1/bin/gradle "$@"
