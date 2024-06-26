from threading import Timer
import sys
import time
import copy
import os
from subprocess import call

class EventLoopDelaySpawn(object):
    """An Event Loop Class That Spawns a Method in a Delayed Thread"""
    def __init__(self,  poll=10,
                        wait=1,
                        verbose=True,
                        dir1="${HOME}/Prog/python/dir1",    # TODO: fix ${HOME} issue
                        dir2="${HOME}/Prog/python/dir2"):   # TODO: fix ${HOME} issue
        self.poll = int(poll)
        self.wait = int(wait)
        self.verbose = verbose
        self.dir1 = dir1
        self.dir2 = dir2

    def poller(self):
        """Creates poll interval"""
        time.sleep(self.poll)
        if self.verbose:
            print("Polling at %s sec interval" % self.poll)


    def action(self):
        if self.verbose:
            print("waiting %s seconds to run Action" % self.wait)
        
        # need to check rsynch man page, the forward slash '/' seems important here
        ret = call("rsync -av --delete %s/ %s" % (self.dir1, self.dir2), shell=True)

    def eventHandler(self):
        #if two directories contain same file names
        if os.listdir(self.dir1) != os.listdir(self.dir2):
            print(os.listdir(self.dir1))
            t = Timer(self.wait,self.action)
            t.start()
            if self.verbose:
                print("Event Registered")
        else:
            if self.verbose:
                print("No Event Registered")

    def run(self):
        """Runs an event loop with a delayed action method"""
        try:
            while True:
                self.eventHandler()
                self.poller()

        except Exception as e:
            print("Error: %s" % e)

        finally:
            sys.exit(0)

E = EventLoopDelaySpawn()
E.run()







