# Singleton design pattern

class SingleObject(object):
    mBuilt = False
    mInstance = None
    # can be called once only
    def __init__(self):
        if SingleObject.mBuilt == True:
            raise Exception("SingleObject: cannot create instance")
        SingleObject.mBuilt = True
    def getInstance():
        if SingleObject.mInstance is None:
            SingleObject.mInstance = SingleObject()
        return SingleObject.mInstance
    def showMessage(self):
        print("The single object is alive and well")
    

object1 = SingleObject.getInstance()
object1.showMessage()

object2 = SingleObject.getInstance()
if(object1 is object2): # id(object1) == id(object2)
    print("The two objects are the same")
        
 
