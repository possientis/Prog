class foo(object):
    def getBar(self): return 23
    def setBar(self,val): pass
    def delBar(self): pass
    bar = property(getBar, setBar, delBar, "This is my doc")
