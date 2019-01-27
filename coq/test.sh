#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq
cd ${HOME}
echo
echo "testing coq..."

./set/test.sh
./zf/test.sh
./sf/test.sh
./cat/test.sh
./hott/test.sh
./systemF/test.sh
./lam/test.sh
./cpdt/test.sh

echo
echo "testing sort..."

# coqtop introduces change of behaviour for -I option between 8.4 and 8.5 
# Need to figure out version number to create portable script
case `coqtop --version | grep '8\.'` in
  *8.4*) VERSION=8.4;;
  *8.6*) VERSION=8.6;;
  *)     VERSION=0;;
esac

# compiling sample library files
cd lib
coqc *.v
cd ..

# running main test file with appropriate 8.4 or 8.5 syntax
if [ ${VERSION} = 8.4 ];
then

  coqtop -batch -l sort.v -I lib

elif [ ${VERSION} = 8.6 ];
then

  coqtop -batch -l sort.v -R lib ''

else

  echo '\ncoqtop version is not supported'
  exit 1

fi

# clean up
./clean.sh
echo "test completed succesfully"
 
cd ${DIR}
echo '\nAll coq tests completed successfully\n'




