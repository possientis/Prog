from subprocess import call
import time
import sys

"""Subtube is a module that simplifies and automates some aspects of subprocess"""

class BaseArgs(object):
    """Base Argument Class that handles keyword argument parsing"""
    def __init__(self, *args, **kwargs):
        self.args = args
        self.kwargs = kwargs
        if self.kwargs.get("delay"):
            self.delay = self.kwargs["delay"]
        else:
            self.delay = 0
        if self.kwargs.get("verbose"):
            self.verbose = self.kwargs["verbose"]
        else:
            self.verbose = False

    def run(self):
        """You must implement a run method"""
        raise NotImplementedError

#x = BaseArgs("abc", 23, suit="nice", delay=45)
#print(x.args)
#print(x.kwargs)
#print(x.delay)
#print(x.verbose)


class Runner(BaseArgs):
    """Simplifies subprocess call and runs call over a sequence of commands

    Runner takes N positional arguments, and optionally:

    [optional keyword parameters]
    delay=1, for time delay in seconds
    verbose=True for verbose output

    Usage:

    cmd = Runner("ls -l", "df -k", verbose=True, delay=3)
    cmd.run()
    """

    def run(self):
        for cmd in self.args:
            if self.verbose:
                print("Running %s with delay=%s" % (cmd, self.delay))
            time.sleep(self.delay)
            call(cmd, shell=True)



