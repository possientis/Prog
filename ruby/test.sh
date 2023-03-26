#!/bin/sh
# need to install ruby and jruby

set -e 
DIR=/home/john/Prog/ruby/
cd ${DIR}

ruby hello.rb
#jruby hello.rb
ruby meta.rb
ruby class.rb
#jruby class.rb

echo '\nAll ruby tests completed successfully\n'
