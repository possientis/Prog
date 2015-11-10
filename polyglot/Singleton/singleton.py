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
    

obj = SingleObject.getInstance()
obj.showMessage()


        
 
