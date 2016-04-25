# Proxy Design Pattern

# This code exercise is borrowed from Design Patterns in C# - 13 Proxy 
# https://www.youtube.com/watch?v=XvbDqLrnkmA

# A proxy is a class which functions as an interface to something else

# There are three participants to the proxy design pattern:
#
# 1. subject
# 2. real subject
# 3. proxy
#

# The subject is the common interface between the real object and proxy
# the real object is that which the proxy is meant to be substituted for

# This is the subject
class ComponentPrice :
    @property
    def CpuPrice(self): raise NotImplementedError
    @property
    def RamPrice(self): raise NotImplementedError
    @property
    def SsdPrice(self): raise NotImplementedError

# This is the real subject
class StoredComponentPrice(ComponentPrice):
    @property
    def CpuPrice(self): return 250.0
    @property
    def RamPrice(self): return 32.0
    @property
    def SsdPrice(self): return 225.0

# This is the proxy
class ProxyComponentPrice(ComponentPrice):
    @property
    def CpuPrice(self) : return self.requestFromServer("CPU")
    @property
    def RamPrice(self) : return self.requestFromServer("RAM")
    @property
    def SsdPrice(self) : return self.requestFromServer("SSD")

    def resquestFromServer(self, request):
        return Server.getInstance().sendRequest(request)

class Server :
    def __init__(self):
        print("Component price server running, awaiting request")
    def getInstance(): return Server._server
    def sendRequest(self, request):
        print("Server receiving request for " + request + " price")




