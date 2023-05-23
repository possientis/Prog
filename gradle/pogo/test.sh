#!/bin/sh

set -e 
DIR=${HOME}/Prog/gradle/pogo/
cd ${DIR}

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

echo '\ntest completed successfully\n'




