#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/pogo/
cd ${HOME}

#gradle -q printVersion
#gradle -q makeReleaseVersionNotCustom
#gradle -q printVersion
#gradle -q makeDebugVersion
#gradle -q printVersion
gradle -q makeReleaseVersion
gradle -q printVersion
gradle -q makeDebugVersion
gradle -q printVersion

echo 'major=0'       >  version.properties
echo 'minor=1'       >> version.properties
echo 'release=false' >> version.properties

cd ${DIR}
echo '\ntest completed successfully\n'




