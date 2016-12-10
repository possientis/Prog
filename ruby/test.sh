#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/ruby/
cd ${HOME}

ruby hello.rb
ruby meta.rb
ruby class.rb

cd ${DIR}
echo '\nAll ruby tests completed successfully\n'




