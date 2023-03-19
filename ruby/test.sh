#!/bin/sh
# need to install ruby and jruby

set -e 
DIR=`pwd`
HOME=/home/john/Prog/ruby/
cd ${HOME}

ruby hello.rb
#jruby hello.rb
ruby meta.rb
ruby class.rb
#jruby class.rb

cd ${DIR}
echo '\nAll ruby tests completed successfully\n'




