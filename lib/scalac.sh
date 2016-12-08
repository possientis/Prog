#!/bin/sh

# create a symbolic link to this file called 'scalac' in /usr/local/bin

# -version output is on stderr which needs to be redirected before pipe
case `/usr/bin/scalac -version 2>&1 | grep '2\.'` in
  *2.11*) VERSION=2.11;;
  *2.9*)  VERSION=2.9;;
  *)      VERSION=0;;
esac

if [ ${VERSION} = 2.11 ];
then

  /usr/bin/scalac "$@"

elif [ ${VERSION} = 2.9 ];
then
  
  env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 /usr/bin/scalac "$@"

else

  echo "\nVERSION=${VERSION}"
  echo '\n/usr/bin/scalac version is not supported'
  exit 1

fi


