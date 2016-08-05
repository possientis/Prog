# xmlrpc server code, run as background process possibly
import xmlrpc.server
import os

def ls(directory):
    try:
        return os.listdir(directory)
    except OSError:
        return []

def ls_boom(directory):
    return os.listdir(directory)

def cb(obj):
    print("OBJECT::", obj)
    print("OBJECT.__class__::", obj.__class__)
    return obj.cb()
    
if __name__ == '__main__':
    s = xmlrpc.server.SimpleXMLRPCServer(('127.0.0.1', 8765))
    s.register_function(ls)
    s.register_function(ls_boom)
    s.register_function(cb)
    s.serve_forever()


