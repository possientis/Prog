from threading import Timer
import sys
import time
import copy

# simple error handling
if len(sys.argv) != 2:
    print("Must enter an interval")
    sys.exit(1)


# our function that we will run
def hello():
    print("Hello, I just got called after %s sec delay" % call_time)

# we spawn our time delayed thread here
delay = int(sys.argv[1])

# the use of copy doesnt add anything in this example, maybe handy
# on mutable objects which we need to pass to or thread
call_time = copy.copy(delay)    # we copy the delay to use later

t = Timer(delay, hello)
t.start()

# we validate that we are not blocked, and that the main program continues
print("waiting %s seconds to run function" % delay)
for x in range(delay):
    print("Main program is still running for %s more sec" % (delay - x))
    time.sleep(1)
