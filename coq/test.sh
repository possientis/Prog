#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq
cd ${HOME}

# coqtop introduces change of behaviour for -I option between 8.4 and 8.5 
# Need to figure out version number to create portable script
case `coqtop --version | grep '8\.'` in
  *8.4*) VERSION=8.4;;
  *8.5*) VERSION=8.5;;
  *)     VERSION=0;;
esac

# compiling sample library files
cd Lib
coqc *.v
cd ..

# running main test file with appropriate 8.4 or 8.5 syntax
if [ ${VERSION} = 8.4 ];
then

  coqtop -batch -l sort.v -I Lib

elif [ ${VERSION} = 8.5 ];
then

  coqtop -batch -l sort.v -R Lib ''

else

  echo '\ncoqtop version is not supported'
  exit 1

fi

# clean up
rm -f Lib/.*.aux
rm -f Lib/*.glob
rm -f Lib/*.vo
 
cd ${DIR}
echo '\nAll coq tests completed successfully\n'




