# can't create a working version of this code (page 182)
# I chose Pyro4 , maybe should try Pyro, moving on...

import Pyro4
import os

class PSAExample(Pyro4.core.ObjBase):
    def ls(self, directory):
        try:
            return os.listdir(directory)
        except OSError:
            return []

        def ls_boom(self, directory):
            return os.listdir(directory)

        def cb(self, obj):
            print("OBJECT:", obj)
            print("OBJECT.__class__:", obj.__class__)
            return obj.cb()

if __name__ == '__main__':
    Pyro4.core.initServer()
    daemon=Pyro.core.Daemon()
    uri=daemon.connect(PSAExample(),"psaexample")
    print("The daemon runs on port:",daemon.port)
    print("The object's uri is:",uri)
