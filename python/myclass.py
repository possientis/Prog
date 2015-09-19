#!/usr/bin/python3

class X(object):
    def __getattr__(self,name):
        print('get',name)
        return 23
    def __setattr__(self,name,value):
        print('set',name,value)
    def foo(self):
        return 0

def main():
    x = X()
    x.foo += 1

if __name__ == '__main__':
    main()



