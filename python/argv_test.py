# creating command line tools with sys.argv does work
# however, it is a far better choice to use the optparse module

import sys

print(sys.argv)

num_args = len(sys.argv) - 1

if num_args == 0:

    sys.stderr.write('Hey, type in an option silly\n')

else:

    print("you typed", num_args, "arguments")

